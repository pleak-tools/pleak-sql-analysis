{-# LANGUAGE MultiParamTypeClasses#-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}

module PostprocessQ where

import Debug.Trace

import Control.Monad
import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import ProgramOptions
import Text.PrettyPrint.Tabulate
import qualified Text.PrettyPrint.Tabulate as T
import qualified GHC.Generics as G
import Data.Data
import Text.Printf
import ErrorMsg

import qualified Banach as B
import qualified BanachQ as BQ
import PolicyQ
import GroupQ

traceIOIfDebug :: Bool -> String -> IO ()
traceIOIfDebug debug msg = do
    if debug then traceIO msg
    else return ()

-- this is used only for nice output printing
data RR = RR {sensitivity :: String, query_result :: String, cauchy_noise :: String, cauchy_relative_err :: String,
              beta :: String, delta :: String, laplace_noise :: String, laplace_relative_err :: String, norm :: String} deriving (Data, G.Generic, Show)

constructRR [v2,v3,v4,v5,v6,v7,v8,v9,v10] = RR {sensitivity = v2,
                                            query_result = v3,
                                            cauchy_noise = v4,
                                            cauchy_relative_err = v5,
                                            beta = v6,
                                            delta = v7,
                                            laplace_noise = v8,
                                            laplace_relative_err = v9,
                                            norm = v10}

-- finds y such that y * exp(y) = x
lambert x 0 = 1
lambert x n =
    let an = lambert x (n - 1) in
    an - (an * exp(an) - x) / ((an + 1) * exp(an))

-- int sqrt(2) / pi * 1 / (1 + x^4) dx
cauchy_integral a =
    let x1 = - log (a**2 - (sqrt 2) * a + 1) in
    let x2 =   log (a**2 + (sqrt 2) * a + 1) in
    let x3 = - 2 * (atan (1 - (sqrt 2) * a)) in
    let x4 =   2 * (atan (1 + (sqrt 2) * a)) in
    (x1 + x2 + x3 + x4) / (4 * pi)

-- int 1 / 2 * exp(-|x|) dx
laplace_integral a =
    1 / 4 * (exp (-a)) * ((exp a - 1)**2 * (- (signum a)) + 2 * (exp a) + (exp (2 * a)) - 1)

-- find the range within which the noise stays with probability p
-- we use window binary search, as we do not have better ideas
find_noise_range_window f p w =
    let q = (f w) - (f (-w)) in
    if p > q then find_noise_range_window f p (w*2)
    else find_noise_range_binary f p 0 w

find_noise_range_binary f p lb ub =
    let a = (ub + lb) / 2 in
    let q = (f a) - (f (-a)) in
    trace (show q ++ "| " ++ show lb ++ " " ++ show a ++ " " ++ show ub) $
    if abs (q - p) < 0.01 then a
    else if p > q then find_noise_range_binary f p a ub
    else find_noise_range_binary f p lb a

compute_epsilon :: Bool -> Double -> Double -> Double -> Double -> Int -> Double
compute_epsilon pos delta a q p nq =

    -- we know that the probability cannot grow above 100%
    if pos then
        let d = min (1 - p) delta in
        - (log (p / (q - p) * (1 / (d + p) - 1))) / (a * fromIntegral nq)
    else
        let d = min (1 - (q - p)) delta in
        - (log ((q - p) / p * (1 / (d + (q - p)) - 1))) / (a * fromIntegral nq)

compute_worst_epsilon :: Double -> Double -> Double -> Int -> Double
compute_worst_epsilon delta a q nq =
    2 / (a * fromIntegral nq) * (log ((sqrt q + sqrt (delta*(delta + q - 1))) / (1 - delta)))

compute_one_comb_data :: Bool -> Int -> Double -> [[Double]] -> [[Bool]] -> [[Double]] -> [Maybe Double] -> [Maybe Double] -> (Double,Double,Double,Double)
compute_one_comb_data pos nq delta ass dss rrss qs' ps =

    -- compute data for each AND
    -- we take 2a as distance since X' may be located somewhere in a corner, except the discrete case
    let as' = map (foldr max 0) $ zipWith (zipWith (\d a -> if d then 1.0 else 2*a)) dss ass in
    let rrs = map (foldr max 0) rrss in

    -- determine the bounds
    let (qs,as) = unzip $ zipWith3 (\q a rr -> if q == Nothing then (1,rr) else (fromJust q, a)) qs' as' rrs in

    -- this is the information about the region within distance a
    let a = foldr max 0 as in
    let q = (product qs) in

    -- compute the epsilon (use worst-case p if p is unknown)
    if elem Nothing ps then 
        let eps = compute_worst_epsilon delta a q nq in
        let p = sqrt q * (exp (eps / 2) - sqrt q) / (exp eps - 1) in
        (a,eps,q,p)
    else
        let p   = (product qs) - (product $ zipWith (-) qs (map fromJust ps)) in
        let eps = compute_epsilon pos delta a q p nq in
        --trace (show qs) $
        --trace (show ps) $
        --trace (show (a,eps,q,p)) $
        --trace ("-------------") $
        (a,eps,q,p)

compute_data :: Bool -> Double -> Double -> [[Double -> Maybe [Double]]] -> [[Bool]] -> [[Double]] -> [[Double]] -> Int -> (Double,Double,Double,Double)
compute_data pos delta starting_a gss dss rss rrss nq =

    -- adjust proposed a to the actual bounds R
    let ass = zipWith (zipWith (\d rr -> if d then rr else min rr starting_a)) dss rrss in

    -- compute the weights (some of them can be unknown)
    let qss = zipWith3 (zipWith3 (\g a r -> g (a*r))) gss ass rss in
    let pss = zipWith  (zipWith  (\g r   -> g r    )) gss rss in

    -- collect all possible variants of q and p
    let cqss = (map (map (\qs -> if elem Nothing qs then Nothing else Just $ product (map fromJust qs))) . allCombsOfLists . map allCombsOfMaybeLists) qss in
    let cpss = (map (map (\ps -> if elem Nothing ps then Nothing else Just $ product (map fromJust ps))) . allCombsOfLists . map allCombsOfMaybeLists) pss in
    let eps  = zipWith (compute_one_comb_data pos nq delta ass dss rrss) cqss cpss in

    let (a,epsilon,q,p) = foldr (\x1@(_,e1,_,_) x2@(_,e2,_,_) -> if e1 < e2 then x1 else x2) (head eps) (tail eps) in
    --trace ("ass: " ++ show ass) $
    --trace ("rss: " ++ show rss) $
    --trace ("qss: " ++ show qss) $
    --trace ("pss: " ++ show pss) $
    --trace ("eps: " ++ show eps) $
    --trace (show (a,epsilon,q,p)) $
    --trace ("-------------") $
    (a,epsilon,q,p)

optimal_a_epsilon :: Bool -> Double -> Double -> [[Double -> Maybe [Double]]] -> [[Bool]] -> [[Double]] -> [[Double]] -> Double -> Double -> Double -> Double
                     -> Double -> Double -> Int -> (Double,Double,Double,Double)
optimal_a_epsilon _ _ _ _ _ _ _ a epsilon q p 0 _ _ = (a,epsilon,q,p)
optimal_a_epsilon pos delta r gss dss rss rrss a epsilon q p k n nq =

    -- compute the initial value for a
    let rr = foldr max 0 (concat rrss) in
    let starting_a = r + k * (rr - r) / n in
    let (a',epsilon',q',p') = compute_data pos delta starting_a gss dss rss rrss nq in

    --take the best values found so far
    let (a'',epsilon'',q'',p'') = if (epsilon' > epsilon) then (a',epsilon',q',p') else (a,epsilon,q,p) in
    optimal_a_epsilon pos delta r gss dss rss rrss a'' epsilon'' q'' p'' (k-1) n nq

-- TODO if we want to look for an optimal beta here using binary search, we will also need outputTableName here
performDPAnalysis :: ProgramOptions -> String -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> M.Map String VarState -> [(String, Maybe Double)] -> [Int] -> IO ()
performDPAnalysis args outputTableName dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

  let debug = not (alternative args)
  let epsilon = getEpsilon args
  let beta    = getBeta args

  -- do not look for optimal beta if it has been specified by the user
  (qmap,taskAggrMap) <- case beta of
          Just _  -> performAnalysis args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts
          Nothing -> do
                         (_,q,tm,_,_) <- findBestBeta args outputTableName epsilon beta dataPath separator initialQuery colNames typeMap taskMap tableExprData attMap colTableCounts
                         return (q,tm)

  traceIOIfDebug debug ("===============================")
  traceIOIfDebug debug ("final qmap: " ++ (show qmap))
  traceIOIfDebug debug ("final taskAggr: " ++ (show taskAggrMap))

  let outMap = M.fromListWith (++) $ concat $ map (\key -> extractFinalResults (qmap ! key) (taskAggrMap ! key) key) (M.keys qmap)
  let outList = map (\((taskName,tableName), zs) -> (taskName,[(tableName,zs)])) $ M.toList outMap
  let taskList = M.toList $ M.fromListWith (++) outList

  let sep1 = if alternative args then [B.unitSeparator] else "\n"
  let sep2 = if alternative args then [B.unitSeparator2] else "\n\n"
  let sep3 = if alternative args then [B.unitSeparator] else "\t"
  let printFloatL = if alternative args then show else printf "%0.6f"
  let printFloatS = if alternative args then show else printf "%0.2f"

  let (_,normsExprs,normsAggrs) = unzip3 $ map BQ.getExtra tableExprData
  let inputTableNames = BQ.getTableNames tableExprData
  let normMap = M.fromList $ zip inputTableNames $ zip normsExprs normsAggrs

  traceIOIfDebug debug ("===============================")
  traceIOIfDebug debug ("Cauchy noise distribution:  add noise 'Cauchy  noise'*z, where z ~ sqrt(2) / pi * 1 / (1 + |x|^4)")
  traceIOIfDebug debug ("Laplace noise distribution: add noise 'Laplace noise'*z, where z ~ 1 / 2 * exp(-x)")
  --traceIOIfDebug debug ("")
  --traceIOIfDebug debug "table name               \tsensitivity\tquery result\tCauchy noise\tCauchy err(%)\tbeta\tdelta\tLaplace noise\tLaplace err(%)"

  let errorUB = errorUBprob args
  let noiseScaleCauchy  = find_noise_range_window cauchy_integral errorUB 1
  let noiseScaleLaplace = find_noise_range_window laplace_integral errorUB 1

  traceIOIfDebug debug ("cauchy scaling: " ++ show noiseScaleCauchy)
  traceIOIfDebug debug ("laplace scaling: " ++ show noiseScaleLaplace)
   

  let taskStr =
          map (\(taskName,res) ->

                  (taskName, (map (\ (tableName, zs) ->
                      let (_,qrs,bs',sdss) = unzip4 zs in
                      let bs  = map ( / noiseScaleCauchy) bs' in
                      let qr  = if length qrs == 1 then printFloatS (head qrs) else "[" ++ intercalate ", " (map printFloatS qrs) ++ "]" in
                      let cauchyError = printFloatL $ (combinedErrs qrs bs sdss) * 100 in
                      let cauchyNoise = (let xs = combinedEtas bs sdss in if length qrs == 1 then printFloatS (head xs) else "[" ++ intercalate ", " (map printFloatS xs) ++ "]") in
                      let sds = printFloatL $ combinedSdss sdss in
                      let norm = if tableName == B.resultForAllTables then
                                      "an l_1-norm of norms w.r.t. all input tables"
                                      -- TODO the following is precise, but is less readable. we also need to remove intermediate tables from the list.
                                      -- "|| " ++ (intercalate "," $ map (\(normExpr,normAggr) -> niceNormPrint normExpr ++ ", rows l_" ++ show normAggr) $ M.elems normMap) ++ " ||_1"
                                 else
                                      let (normExpr,normAggr) = (normMap ! tableName) in
                                      let mainNorm = niceNormPrint normExpr in
                                      if mainNorm == "" then "--" else niceNormPrint normExpr ++ ", rows l_" ++ niceADoublePrint normAggr
                      in

                      -- these betas should all be the same in our implementation, otherwise DP w.r.t. several outputs is not well-defined
                      let preciseBetas = map (\b -> epsilon / (4 + 1) - b) bs in
                      let finalBeta    = printFloatL $ foldr max 0 preciseBetas in
                      let laplaceBs' = map (\beta -> epsilon - beta) preciseBetas in
                      let laplaceBs = map (/ noiseScaleLaplace) laplaceBs' in
                      let laplaceDeltas = zipWith (\beta b -> if beta == 0 then exp(-2) else 2*exp(epsilon-(1 + (epsilon - b) / beta))) preciseBetas laplaceBs' in
                      let laplaceDelta = printFloatL $ foldr max 0 laplaceDeltas in
                      let laplaceError = printFloatL $ (combinedErrs qrs laplaceBs sdss) * 100 in
                      --let laplaceNoise = (let xs = map (* 1.515) (combinedEtas laplaceBs sdss) in if length qrs == 1 then printFloatS (head xs) else "[" ++ intercalate ", " (map printFloatS xs) ++ "]") in
                      let laplaceNoise = (let xs = combinedEtas laplaceBs sdss in if length qrs == 1 then printFloatS (head xs) else "[" ++ intercalate ", " (map printFloatS xs) ++ "]") in
                      [tableName,sds,qr,cauchyNoise,cauchyError,finalBeta,laplaceDelta,laplaceNoise,laplaceError,norm]) res)

          )) taskList

  when (alternative args) $ putStrLn $ intercalate sep2 $ map (\(taskName, xss) -> taskName ++ sep1 ++ intercalate sep1 (map (\xs -> intercalate sep3 xs) xss)) taskStr
  forM taskStr $ \(taskName,tableMap) -> do
          when debug $ putStrLn ("-------------------------\nTask: " ++ taskName)
          let tableResultMap = M.fromList $ map (\(v : vs) -> (v, constructRR vs)) tableMap
          when debug $ T.printTable tableResultMap
  putStr ""


performPolicyAnalysis :: ProgramOptions -> String -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [BQ.DataWrtTable] -> [(M.Map String VarState, Double)] -> M.Map String VarState -> [Int] -> IO ()
performPolicyAnalysis args outputTableName dataPath separator initialQuery colNames typeMap taskMap tableExprData plcMaps attMap colTableCounts = do

  -- the input epsilon now works as delta, the upper bound on attacker's advantage
  let debug = not (alternative args)
  let delta = getEpsilon args
  let fixedBeta = getBeta args
  let nq = numOfQueries args -- this basically scales epsilon nq times, assuming that up to nq queries may be run on the same data

  -- process the policy and the attacker knowledge
  let plainTypeMaps = map (\(tname,tmap) -> map (\(x,y) -> (preficedVarName tname x,y)) tmap) typeMap
  let plainTypeMap  = M.fromList $ concat plainTypeMaps

  -- we rather assume that there is one leak-statement per policy, but if there are many, all of them have the same delta and can be summed up
  let cost = sum $ map snd plcMaps

  --remove the special variables that are not needed
  let kwlen = length reservedSensRowsKeyword
  let plcMapData = map (M.filterWithKey (\varName _ -> length varName < kwlen || reverse (take kwlen (reverse varName)) /= reservedSensRowsKeyword) . fst) plcMaps

  let bss  = map (extract_bs attMap) plcMapData
  let gss    = zipWith filterWith bss $ map (extract_gs attMap) plcMapData
  let dss    = zipWith filterWith bss $ map (extract_ds attMap) plcMapData
  let rss    = zipWith filterWith bss $ map (extract_rs attMap) plcMapData
  let rrss'  = zipWith filterWith bss $ map (extract_Rs attMap plainTypeMap) plcMapData

  -- this norm is used only to show it in the output
  let norm = deriveDbNorm attMap plcMapData

  -- further, we assume r = 1 everywhere in each dimension
  let rrss = zipWith (zipWith (/)) rrss' rss --rescaled R
  let r = 1

  -- space dimensionality comes from the total number of sensitive variables
  -- we multiply the dimensions of variables belonging to one sensitive set
  -- we add the weights of different sensitive sets, since the attacker may guess any of them
  -- TODO do not include repeating variables multiple times into the intersection weight
  let allSensVars = S.fromList $ concat (map M.keys plcMapData)

  -- it seems that brute-forcing optimal epsilon and a works quite well
  -- we consider multidimensional space, where the radius is linf-norm
  let num_of_tries = 10000

  -- since 'a' is only an estimation parameter, we find the noise separately for the positive and the negative guess, and then take the largest noise
  let (init_a, init_epsilon, init_q, init_p) = compute_data True delta (foldr max 0 (concat rrss)) gss dss rss rrss nq
  let (a1,epsilon1,q1,p1) = optimal_a_epsilon True delta r gss dss rss rrss init_a init_epsilon init_q init_p num_of_tries num_of_tries nq

  let (init_a, init_epsilon, init_q, init_p) = compute_data False delta (foldr max 0 (concat rrss)) gss dss rss rrss nq
  let (a0,epsilon0,q0,p0) = optimal_a_epsilon False delta r gss dss rss rrss init_a init_epsilon init_q init_p num_of_tries num_of_tries nq

  let epsilon = min epsilon0 epsilon1

  {-
  -- this computation works only for uniform distribtions
  -- convert guessing probability to epsilon (assuming that 'a' is optimal)
  let ub = p + d
  let es' = map (\r -> (lambert (ub / (exp(1) * (1 - ub))) 10) / r) rs
  -- consider scaled dimensions, where r = 1 for all r
  let epsilon' = if m == 1 then lambert (ub / (exp(1) * (1 - ub))) 10 else m / (exp(1) * (1 / ub - 1 + exp(-m)) ** (1 / m))

  -- find the initial (optimal) value of a
  -- we compute a = m / epsilon + 1 if m = 1, and m / epsilon for the multidimensional case
  let a' = if m == 1 then m / epsilon' + 1 else m / epsilon'
  -}

  traceIOIfDebug debug ("plcMaps: " ++ show plcMaps)
  traceIOIfDebug debug ("allSensVars: " ++ show allSensVars)
  traceIOIfDebug debug ("--------")
  traceIOIfDebug debug ("delta: " ++ (show delta))
  traceIOIfDebug debug ("--------")
  traceIOIfDebug debug ("rrss': " ++ (show rrss'))
  traceIOIfDebug debug ("rss: " ++ (show rss))
  traceIOIfDebug debug ("rrss: " ++ (show rrss))
  traceIOIfDebug debug ("r: " ++ (show r))
  traceIOIfDebug debug ("--------")
  traceIOIfDebug debug ("a0: " ++ (show a0))
  traceIOIfDebug debug ("eps0: " ++ (show epsilon0))
  traceIOIfDebug debug ("q0: " ++ (show q0))
  traceIOIfDebug debug ("p0: " ++ (show p0))
  traceIOIfDebug debug ("--------")
  traceIOIfDebug debug ("a1: " ++ (show a1))
  traceIOIfDebug debug ("eps1: " ++ (show epsilon1))
  traceIOIfDebug debug ("q1: " ++ (show q1))
  traceIOIfDebug debug ("p1: " ++ (show p1))

  -- if delta < prior, then the lower bound may be negative, and we take the bound 0 in this case
  let pr_pre  = p1 * 100
  let pr_post = [max 0 (q0 - 1 / (1 + exp(- a0 * epsilon0 * (fromIntegral nq)) * p0 / (q0-p0))) * 100, 1 / (1 + exp(- a1 * epsilon1 * (fromIntegral nq)) * (q1-p1) / p1) * 100]

  (finalBeta,finalQmap,finalTaskAggr,finalError,_) <- findBestBeta args outputTableName epsilon fixedBeta dataPath separator initialQuery colNames typeMap taskMap tableExprData attMap colTableCounts

  traceIOIfDebug debug ("===============================")
  traceIOIfDebug debug ("final qmap: " ++ (show finalQmap))
  traceIOIfDebug debug ("final taskAggr: " ++ (show finalTaskAggr))

  let expectedCost = delta * cost
  traceIOIfDebug debug ("params: beta=" ++ (show finalBeta) ++ ", eps=" ++ (show epsilon))

  -- additional outputs
  let (finalQrs, finalBs, finalSdss) = unzip3 $ map (\key -> extractFinalResult (finalQmap ! key) (finalTaskAggr ! key) B.resultForAllTables outputTableName) (M.keys finalQmap)
  let cauchyNoise = combinedEtas finalBs finalSdss
  --let cauchyError = combinedErrs finalQrs finalBs finalSdss -- we already have this

  -- TODO we would like to compute epsilon for Laplace noise, which is different since there is epsilon-delta DP
  -- we need to find a way of converting GA to epsilon and delta
  --let preciseBetas = map (\b -> epsilon / (4.0 + 1) - b) finalBs
  --let laplaceBs = map (\beta -> epsilon - beta) preciseBetas
  --let laplaceDeltas = zipWith (\beta b -> exp(-(1 + (epsilon - b) / beta))) preciseBetas laplaceBs
  --let laplaceDelta = foldr max 0 laplaceDeltas
  --let laplaceError = combinedErrs finalQrs laplaceBs finalSdss
  --let laplaceNoise = combinedEtas laplaceBs finalSdss

  --putStrLn $ intercalate (if alternative args then [B.unitSeparator2] else "\n\n") [show (pr_pre * 100.0), show (pr_post * 100.0), show expectedCost, show (finalError * 100.0)]

  let errorUB = errorUBprob args
  let noiseScaleCauchy  = find_noise_range_window cauchy_integral errorUB 1
  let noiseScaleLaplace = find_noise_range_window laplace_integral errorUB 1

  traceIOIfDebug debug ("cauchy scaling: " ++ show noiseScaleCauchy)
  traceIOIfDebug debug ("laplace scaling: " ++ show noiseScaleLaplace)

  traceIOIfDebug debug ("===============================")
  let outputList = [("prior: ",                         show pr_pre),
                    ("posterior: ",                     show pr_post),
                    ("expected cost: ",                 show expectedCost),
                    (show (round $ errorUB * 100) ++ "%-realtive error (Cauchy noise): ", show (finalError * noiseScaleCauchy * 100.0)),
                    ("Cauchy noise magnitude: a <- ",   show (map ( * noiseScaleCauchy) cauchyNoise)),
                    ("Cauchy noise distribution: ",     "add noise a*z, where z ~ sqrt(2) / pi * 1 / (1 + |x|^4)"),

                    -- the scaling by 1.515 is needed to get a 78% error as in Cauchy case
                    --("78%-realtive error (Laplace noise): ", show (laplaceError * 100.0 * 1.515)),
                    --("Laplace noise magnitude (a): ",    show (map (* 1.515) laplaceNoise)),
                    --("Laplace noise distribution:",      "add noise a*z, where z ~ 1 / 2 * exp(-x)"),
                    --("delta (Laplace only): ",      show laplaceDelta),

                    ("DP epsilon: ",                   show epsilon),
                    ("smoothness beta: ",                      show finalBeta),
                    ("sensitivity w.r.t. norm N: ", show finalSdss),
                    ("norm N: ",                    niceNormPrint norm)]

  let sep = if alternative args then [B.unitSeparator2] else "\n"
  let out = if alternative args then map snd outputList else map (\(x,y) -> x ++ y) outputList
  putStrLn $ intercalate sep out


-- TODO it seems that we can remove sds (and maybe something else) since this is already a part of qmap
findBestBeta :: ProgramOptions -> String -> Double -> Maybe Double -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [BQ.DataWrtTable] -> M.Map String VarState -> [Int] -> IO (Double, M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double, [Double])
findBestBeta args outputTableName epsilon fixedBeta dataPath separator initialQuery colNames typeMap taskMap tableExprData attMap colTableCounts = do

  let step = performAnalysisBetaStep args outputTableName epsilon dataPath separator initialQuery colNames typeMap taskMap [] tableExprData attMap [] colTableCounts
  (finalBeta,finalQmap,finaltaskAggr,finalError,finalSds) <- case fixedBeta of
                    Nothing -> do
                        initialBeta <- BQ.findMinimumBeta args epsilon Nothing dataPath separator initialQuery colNames typeMap [] tableExprData attMap [] colTableCounts
                        (initialQmap,initialTaskAggr,initialError,initialSds) <- step (Just initialBeta)
                        repeatUntilGetBestError step initialError initialBeta (epsilon / 5.0) initialBeta initialQmap initialTaskAggr initialError initialSds
                    Just beta' -> do
                        (qmap',taskAggr',err',sds') <- step (Just beta')
                        return (beta', qmap',taskAggr', err',sds')
  return (finalBeta,finalQmap,finaltaskAggr,finalError,finalSds)

repeatUntilGetBestError :: (Maybe Double -> IO (M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])],Double, [Double])) -> Double -> Double -> Double -> Double -> M.Map [String] Double -> M.Map [String] [(String, [(String, (Double, Double))])] -> Double -> [Double] -> IO (Double, M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double, [Double])
repeatUntilGetBestError step prevError betaMin betaMax bestBeta bestQmap bestTaskAggr bestError bestSds = do
    let nextBeta = (betaMax + betaMin) / 2.0
    (nextQmap, nextTaskAggr, nextError, nextSds) <- step (Just nextBeta)
    let (bestBeta', bestQmap', bestTaskAggr', bestError', bestSds') = if nextError < bestError then (nextBeta, nextQmap, nextTaskAggr, nextError, nextSds) else (bestBeta, bestQmap, bestTaskAggr, bestError, bestSds)
    if (betaMax - betaMin > 0.01) && (betaMax > 0.01) && (betaMin /= 1/0) && (betaMax /= 1/0)
      then do
        --do binary search
        if (prevError <= nextError) then do
            repeatUntilGetBestError step prevError betaMin nextBeta bestBeta' bestQmap' bestTaskAggr' bestError' bestSds'
        else do
            repeatUntilGetBestError step nextError nextBeta betaMax bestBeta' bestQmap' bestTaskAggr' bestError' bestSds'
      else do
        return (bestBeta', bestQmap', bestTaskAggr', bestError', bestSds')

-- if we have several final groups, we combine errors into an l2-norm of errors
extractFinalResults :: Double -> [(String, [(String, (Double, Double))])] -> [String] -> [((String,String),[([String], Double, Double, Double)])]
extractFinalResults qr taskAggr key =
    concat $ map (\(taskName,res) -> map (\ (tableName, (b,sds)) -> ((taskName,tableName), [(key, qr, b, sds)])) res   ) taskAggr

extractFinalResult :: Double -> [(String, [(String, (Double, Double))])] -> String -> String -> (Double,Double,Double)
extractFinalResult qr taskAggr taskName tableName =

  let resultMap = M.fromList $ (M.fromList taskAggr) ! tableName in
  let (b, sds) = resultMap ! taskName in
  (qr, b, sds)

combinedSdss :: [Double] -> Double
combinedSdss sdss = sum sdss

combinedEtas :: [Double] -> [Double] -> [Double]
combinedEtas bs sdss = zipWith (\b sds -> (sds / b)) bs sdss

combinedErrs :: [Double] -> [Double] -> [Double] -> Double
combinedErrs qrs bs sdss =
    let qnorm   = sqrt $ sum $ map (^2) qrs in
    let errnorm = sqrt $ sum $ map (^2) $ combinedEtas bs sdss in
    errnorm / qnorm
    --sqrt $ sum $ zipWith3 (\qr b sds -> ((sds / b) / qr) ^ 2) qrs bs sdss

performAnalysisBetaStep :: ProgramOptions -> String -> Double -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> M.Map String VarState -> [(String, Maybe Double)] -> [Int] -> Maybe Double -> IO (M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double, [Double])
performAnalysisBetaStep args outputTableName epsilon dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts beta = do

  (qmap,taskAggrMap) <- performAnalysis args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts
  let (qrs, bs, sdss) = unzip3 $ map (\key -> extractFinalResult (qmap ! key) (taskAggrMap ! key) B.resultForAllTables outputTableName) (M.keys qmap)
  let err = combinedErrs qrs bs sdss

  return (qmap,taskAggrMap,err,sdss)


performAnalysis :: ProgramOptions -> Double -> Maybe Double -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> M.Map String VarState -> [(String, Maybe Double)] -> [Int] -> IO (M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])])
performAnalysis args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

  (qmap,taskAggrMap') <- BQ.performAnalyses args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts

  -- if we choose beta that is not compatible with epsilon during optimization, we get a negative b, so we set it to 0 to get Infinity relative error
  -- in policy analysis, this means that desired epsilon, and hence the guessing advantage bound, could not be achieved
  let taskAggrMap = M.fromList $ map (\(key,taskAggrGroup) -> (key, map (\(taskName,res) -> (taskName, map (\ (tableName, (b,sds)) -> (tableName, (max b 0, sds)) ) res)) taskAggrGroup)) (M.toList taskAggrMap')
  return (qmap, taskAggrMap)

allCombsOfLists [] = [[]]
allCombsOfLists (xs:xss) =
    [(y:ys) | y <- xs, ys <- allCombsOfLists xss]

allCombsOfMaybeLists :: [Maybe [a]] -> [[Maybe a]]
allCombsOfMaybeLists [] = [[]]
allCombsOfMaybeLists (xs:xss) =
    concat [z | ys <- allCombsOfMaybeLists xss, let z = case xs of {Nothing -> [(Nothing : ys)]; _ -> [((Just y) : ys) | y <- (fromJust xs)]}]
