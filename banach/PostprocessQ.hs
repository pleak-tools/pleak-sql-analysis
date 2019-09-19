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
import Numeric
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

niceRound x = fromIntegral (round (x * 1000)) / 1000

-- lambert's W function: finds y such that y * exp(y) = x
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
    if abs (q - p) < 0.01 then a
    else if p > q then find_noise_range_binary f p a ub
    else find_noise_range_binary f p lb a

compute_epsilon :: Bool -> Double -> Double -> Double -> Double -> Int -> Double
compute_epsilon pos ga a q p nq =

    -- we know that the probability cannot grow above 100%
    if pos then
        let d = min (1 - p) ga in
        - (log (p / (q - p) * (1 / (d + p) - 1))) / (a * fromIntegral nq)
    else
        let d = min (1 - (q - p)) ga in
        - (log ((q - p) / p * (1 / ((1 - p) / (q - p) * (d + (1 - p) - (1 - q) / (1 - p))) - 1))) / (a * fromIntegral nq)
        -- - (log ((q - p) / p * (1 / (d + (q - p)) - 1))) / (a * fromIntegral nq)

compute_worst_epsilon :: Double -> Double -> Double -> Int -> Double
compute_worst_epsilon ga a q nq =
    2 / (a * fromIntegral nq) * (log ((sqrt q + sqrt (ga*(ga + q - 1))) / (1 - ga)))

-- we know that, if the variable is the same, then only the r part can be different
minPlcData (PlcData b ur r1 rr d g) (PlcData _ _ r2 _ _ _) =
    (PlcData b ur (min r1 r2) rr d g)

-- if the same variable repeats with different precisions, we need to take minimum in an AND
fand :: [(Int, M.Map [String] PlcData)] -> [(Int, M.Map [String] PlcData)] -> [(Int, M.Map [String] PlcData)]
fand ms1 ms2 = concat $ map (\(s2,m2) -> map (\(s1,m1) -> (s1*s2, M.unionWith minPlcData m1 m2)) ms1) ms2

for  :: [(Int, M.Map [String] PlcData)] -> [(Int, M.Map [String] PlcData)] -> [(Int, M.Map [String] PlcData)]
for ms1 ms2 = ms1 ++ ms2 ++ map (\(s,v) -> (-s,v)) (fand ms1 ms2)

compute_eps_for_a :: Bool -> Double -> PlcMap -> Double -> Int -> (Double,Double,Double,Double)
compute_eps_for_a pos ga expr sample_a nq =


    -- compute p and q using the equalities and P(A || B) = P(A) + P(B) - P(AB), P(AA) = P(A), P(AB) = P(A)*P(B)
    let pqExpr = traverseExpr fand for (\x -> if x == 1 then [(1,M.empty)] else []) (\(var,pd) -> [(1, M.singleton var pd)]) expr in

    -- compute the weight of X' (distributions of some dimensions can be unknown)
    -- if different elements come with different probabilities, we consider all combinations
    let qssAs = map (\(s,m) -> let (vss,as) = unzip $ map (\(PlcData b ur r rr d g) ->

                                    -- adjust proposed a to the actual bounds R
                                    -- we take 2a as distance since X' may be located somewhere in a corner, except the discrete case
                                    let a = if not b then sample_a
                                            else if d then rr
                                            else max r $ min rr sample_a
                                    in
                                            if not b then ([1], sample_a)
                                            else
                                                case g (ur * a) of
                                                    -- TODO something is still wrong with 'Nothing' case
                                                    Nothing -> ([1], if d then 1.0 else rr)
                                                    Just vs -> (vs,  if d then 1.0 else 2*a)
                                    ) (M.elems m)
                               in
                                    (map (((fromIntegral s) * ) . product) (allCombsOfLists vss), foldr max 1 as)) pqExpr
    in

    let pss'  = map (\(s,m) -> let vss = map (\(PlcData b ur r _ _ g) -> if b then g (ur * r) else Just [1]) (M.elems m) in
                               if elem Nothing vss then Nothing
                               else
                                    let wss = allCombsOfLists $ (map fromJust) vss in
                                    Just $ map ((((fromIntegral s) *) . product) ) wss) pqExpr
    in

    -- determine the unique bound a that is true for all dimensions
    let (qss',as) = unzip qssAs in
    let a = foldr max 1 as in

    let pss = allCombsOfMaybeLists pss' in
    let qss = allCombsOfLists qss' in

    -- compute the epsilon (use worst-case p if p is unknown)
    let results = zipWith (\ps qs ->
                       let q = sum qs in
                       if elem Nothing ps then
                               let eps = compute_worst_epsilon ga a q nq in
                               let p = min q ((sqrt q) * ((exp (eps / 2)) - (sqrt q)) / ((exp eps) - 1)) in
                               (a,eps,q,p)
                       else
                               let p = sum (map fromJust ps) in
                               let eps = compute_epsilon pos ga a q p nq in
                               (a,eps,q,p)
                  ) pss qss
    in

    let (a,epsilon,q,p) = foldr (\x1@(_,e1,_,_) x2@(_,e2,_,_) -> if e1 < e2 then x1 else x2) (head results) (tail results) in
    (a,epsilon,q,p)


optimal_a_epsilon :: Bool -> Double -> Double -> Double -> PlcMap -> Double -> Double -> Double -> Double
                     -> Double -> Double -> Int -> (Double,Double,Double,Double)
optimal_a_epsilon _ _ _ _ _ a epsilon q p 0 _ _ = (a,epsilon,q,p)
optimal_a_epsilon pos ga scaled_r scaled_rr expr a epsilon q p k n nq =

    -- compute the sample value for a and check how good it is
    let sample_a = scaled_r + k * (scaled_rr - scaled_r) / n in
    let (a',epsilon',q',p') = compute_eps_for_a pos ga expr sample_a nq in

    --take the best values found so far
    let (a'',epsilon'',q'',p'') = if (epsilon' > epsilon) then (a',epsilon',q',p') else (a,epsilon,q,p) in
    optimal_a_epsilon pos ga scaled_r scaled_rr expr a'' epsilon'' q'' p'' (k-1) n nq


performDPAnalysis :: ProgramOptions -> String -> String -> String -> String -> [String] -> Int -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> AttMap -> [(String, Maybe Double)] -> [Int] -> IO ()
performDPAnalysis args outputTableName dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

  let debug    = not (alternative args)
  let epsilon' = getEpsilon args
  let beta     = getBeta args
  let delta    = getDelta args

  -- do not look for optimal beta if it has been specified by the user
  (qmap,taskAggrMap) <- case beta of
          Just _  -> performAnalysis args epsilon' beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts
          Nothing -> do
                         (_,q,tm,_,_) <- findBestBeta args outputTableName epsilon' beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap tableExprData attMap colTableCounts
                         return (q,tm)

  -- if we have a GroupBy query, we need to scale epsilon accordingly
  let epsilon = epsilon' / (fromIntegral numOfOutputs)

  traceIOIfDebug debug ("===============================")
  traceIOIfDebug debug ("final qmap: " ++ (show qmap))
  traceIOIfDebug debug ("final taskAggr: " ++ (show taskAggrMap))

  -- TODO if a group is empty, we set its output to 0, but it is actually difficult to define for MIN/MAX queries
  let outMap = M.fromListWith (++) $ concat $ map (\key -> extractFinalResults (if M.member key qmap then qmap ! key else 0) (taskAggrMap ! key) key) (M.keys taskAggrMap)
  let outList = map (\((taskName,tableName), zs) -> (taskName,[(tableName,zs)])) $ M.toList outMap
  let taskList = M.toList $ M.fromListWith (++) outList

  let sep1 = if alternative args then [B.unitSeparator] else "\n"
  let sep2 = if alternative args then [B.unitSeparator2] else "\n\n"
  let sep3 = if alternative args then [B.unitSeparator3] else "\t"
  let printFloatL = if alternative args then show else printf "%0.6f"
  let printFloatS = if alternative args then show else printf "%0.2f"
  let printFloatE = if alternative args then show else (\x -> showEFloat (Just 2) x "")

  let (_,normsExprs,normsAggrs) = unzip3 $ map BQ.getExtra tableExprData
  let inputTableNames = BQ.getTableNames tableExprData
  let normMap = M.fromList $ zip inputTableNames $ zip normsExprs normsAggrs

  traceIOIfDebug debug ("===============================")
  traceIOIfDebug debug ("Cauchy noise distribution:  add noise 'Cauchy  noise'*z, where z ~ sqrt(2) / pi * 1 / (1 + |x|^4)")
  traceIOIfDebug debug ("Laplace noise distribution: add noise 'Laplace noise'*z, where z ~ 1 / 2 * exp(-x)")

  let errorUB = errorUBprob args
  let noiseScaleCauchy  = find_noise_range_window cauchy_integral errorUB 1
  let noiseScaleLaplace = find_noise_range_window laplace_integral errorUB 1

  traceIOIfDebug debug ("cauchy scaling: " ++ show noiseScaleCauchy)
  traceIOIfDebug debug ("laplace scaling: " ++ show noiseScaleLaplace)

  let taskStr =
          map (\(taskName,res) ->

                  (taskName, (map (\ (tableName, zs) ->
                      let (_,qrs,bs,sdss) = unzip4 zs in
                      let qr  = if length qrs == 1 then printFloatS (head qrs) else "[" ++ intercalate ", " (map printFloatS qrs) ++ "]" in
                      let cauchyError = printFloatL $ (combinedErrs qrs bs sdss) * noiseScaleCauchy * 100 in
                      let cauchyNoise = (let xs = map (* noiseScaleCauchy) (combinedEtas bs sdss) in if length qrs == 1 then printFloatS (head xs) else "[" ++ intercalate ", " (map printFloatS xs) ++ "]") in
                      let sds = printFloatL $ combinedSdss sdss in
                      let norm = if tableName == B.resultForAllTables then
                                      "an l_1-norm of all input table norms"
                                      -- TODO the following is precise, but is less readable. we also need to remove intermediate tables from the list.
                                      -- "|| " ++ (intercalate "," $ map (\(normExpr,normAggr) -> niceNormPrint normExpr ++ ", rows l_" ++ show normAggr) $ M.elems normMap) ++ " ||_1"
                                 else
                                      let (normExpr,normAggr) = (normMap ! tableName) in
                                      let mainNorm = niceNormPrint normExpr in
                                      if mainNorm == "" then "--" else niceNormPrint normExpr ++ ", rows l_" ++ niceADoublePrint normAggr
                      in

                      -- these betas should all be the same in our implementation, otherwise DP w.r.t. several outputs is not well-defined
                      let allBetas = map (\b -> epsilon / (4 + 1) - b) bs in
                      let finalBeta    = printFloatL $ foldr max 0 allBetas in

                      -- if beta = 0, we get delta = 0 and b = eps - beta
                      let deltaLB = 2*exp(epsilon-1-epsilon / (foldr max 0 allBetas)) in

                      let laplaceDeltas = map (\beta    -> if deltaLB == 0 then 0 else max delta deltaLB) allBetas in
                      let laplaceBs = zipWith (\beta d  -> if deltaLB == 0 then epsilon - beta else log ((d / deltaLB)**beta)) allBetas laplaceDeltas in

                      let laplaceDelta   = printFloatE $ foldr min (1/0) laplaceDeltas in

                      --trace ("laplace bs1: " ++ show laplaceBs) $

                      let laplaceError = printFloatL $ (combinedErrs qrs laplaceBs sdss) * noiseScaleLaplace * 100 in
                      let laplaceNoise = (let xs =  map (* noiseScaleLaplace) (combinedEtas laplaceBs sdss) in if length qrs == 1 then printFloatS (head xs) else "[" ++ intercalate ", " (map printFloatS xs) ++ "]") in
                      [tableName,sds,qr,cauchyNoise,cauchyError,finalBeta,laplaceDelta,laplaceNoise,laplaceError,norm]) res)

          )) taskList

  when (alternative args) $ putStrLn $ intercalate sep2 $ map (\(taskName, xss) -> taskName ++ sep1 ++ intercalate sep1 (map (\xs -> intercalate sep3 xs) xss)) taskStr
  forM taskStr $ \(taskName,tableMap) -> do
          when debug $ putStrLn ("-------------------------\nTask: " ++ taskName)
          let tableResultMap = M.fromList $ map (\(v : vs) -> (v, constructRR vs)) tableMap
          when debug $ T.printTable tableResultMap
  putStr ""


performPolicyAnalysis :: ProgramOptions -> String -> String -> String -> String -> [String] ->Int -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [BQ.DataWrtTable] -> PlcCostType -> AttMap -> [Int] -> IO ()
performPolicyAnalysis args outputTableName dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap tableExprData plcCostType attMap colTableCounts = do

  let plcExpr = getStatement plcCostType
  let cost = getCost plcCostType

  -- the input epsilon now works as GA, the upper bound on attacker's advantage
  let debug = not (alternative args)
  let ga = getEpsilon args
  let fixedBeta = getBeta args

  -- this basically scales epsilon nq times, assuming that up to nq queries may be run on the same data
  -- we actually have numOfOutputs as well, but that will be taken into account by Banach analyser
  let nq = numOfQueries args

  -- process the policy and the attacker knowledge
  let plainTypeMaps = map (\(tname,tmap) -> map (\(x,y) -> (preficedVarName tname x,y)) tmap) typeMap
  let plainTypeMap  = M.fromList $ concat plainTypeMaps

  -- compute parameters of the sensitivie attributes
  let unit_r_map =  traverseExpr (M.unionWith min) (M.unionWith min) (const M.empty) (\(var,plcState) ->
                                   let r  = extract_r plcState in
                                   M.singleton var r) plcExpr

  let plcExprExt = rewriteExpr (\(var,plcState) ->
                                     let b  = extract_b attMap plcState var in
                                     let r  = extract_r plcState in
                                     let rr = extract_R attMap plainTypeMap plcState var in
                                     let d  = extract_d plcState in
                                     let g  = extract_g attMap var in
                                     let unit_r = unit_r_map ! var in
                                     (var, PlcData b unit_r (r / unit_r) (rr / unit_r) d g)) plcExpr

  -- further, we assume r = 1 everywhere in each dimension
  let scaled_r  = 1
  let scaled_rr = traverseExpr max max (const 0) (\(var,plcState) -> let r  = extract_r plcState in
                                                                     let rr = extract_R attMap plainTypeMap plcState var in
                                                                     rr / r) plcExpr

  -- this norm is used only to show it in the output
  let norm = deriveDbNorm attMap plcExpr
  let allSensVars = extract_vars plcExpr

  -- it seems that brute-forcing optimal epsilon and a works quite well
  -- we consider multidimensional space, where the radius is linf-norm
  let num_of_tries = 10000

  -- since 'a' is only an estimation parameter, we find the noise separately for the positive and the negative guess, and then take the largest noise
  let (init_a, init_epsilon, init_q, init_p) = compute_eps_for_a True ga plcExprExt scaled_rr nq
  let (a1,epsilon1,q1,p1) = optimal_a_epsilon True ga scaled_r scaled_rr plcExprExt init_a init_epsilon init_q init_p num_of_tries num_of_tries nq

  let (init_a, init_epsilon, init_q, init_p) = compute_eps_for_a False ga plcExprExt scaled_rr nq
  let (a0,epsilon0,q0,p0) = optimal_a_epsilon False ga scaled_r scaled_rr plcExprExt init_a init_epsilon init_q init_p num_of_tries num_of_tries nq

  let epsilon' = min epsilon0 epsilon1

  traceIOIfDebug debug ("plcExpr: " ++ show plcExpr)
  traceIOIfDebug debug ("plcExprExt: " ++ show plcExprExt)
  traceIOIfDebug debug ("allSensVars: " ++ show allSensVars)
  traceIOIfDebug debug ("--------")
  traceIOIfDebug debug ("GA: " ++ (show ga))
  traceIOIfDebug debug ("--------")
  traceIOIfDebug debug ("scaled rr: " ++ (show scaled_rr))
  traceIOIfDebug debug ("scaled r: " ++ (show scaled_r))
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

  let pr_pre  = p1 * 100
  let pr_post = 1 / (1 + exp(- a1 * epsilon1 * (fromIntegral nq)) * (q1-p1) / p1) * 100

  -- the following output is more informative, but less understandable
  -- if ga < prior, then the lower bound may be negative, and we take the bound 0 in this case
  --let pr_post = [max 0 (q0 - 1 / (1 + exp(- a0 * epsilon0 * (fromIntegral nq)) * p0 / (q0-p0))) * 100, 1 / (1 + exp(- a1 * epsilon1 * (fromIntegral nq)) * (q1-p1) / p1) * 100]

  (finalBeta,qmap,taskAggrMap,cauchyError,_) <- findBestBeta args outputTableName epsilon' fixedBeta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap tableExprData attMap colTableCounts

  traceIOIfDebug debug ("===============================")
  traceIOIfDebug debug ("final qmap: " ++ (show qmap))
  traceIOIfDebug debug ("final taskAggr: " ++ (show taskAggrMap))

  -- if we have a GroupBy query, we need to scale epsilon accordingly
  -- we already took into account numOfQueries, now we also need to include numOfOutputs
  -- TODO check why we redefined numOfOutputs earlier, as done in the next line
  -- let numOfOutputs = fromIntegral $ length finalQrs
  let epsilon = epsilon' / (fromIntegral numOfOutputs)

  --let expectedCost = ga * cost
  traceIOIfDebug debug ("Cauchy params: beta=" ++ (show finalBeta) ++ ", eps=" ++ (show epsilon))

  -- additional outputs
  let (finalQrs, cauchyBs, finalSdss) = unzip3 $ map (\key -> extractFinalResult (if M.member key qmap then qmap ! key else 0) (taskAggrMap ! key) B.resultForAllTables outputTableName) (M.keys taskAggrMap)
  let cauchyNoise = combinedEtas cauchyBs finalSdss


  -- (epsilon,delta)-DP related stuff:

  -- we restore the betas that have been computed before (these betas are not cauchy-specific)
  -- if beta = 0, we get delta = 0
  let allBetas = map (\b -> epsilon / (4 + 1) - b) cauchyBs
  let (laplaceEpsilons,laplaceBs) = unzip $ zipWith3 (\sds beta b -> if epsilon < 1/0 then findOptimalB sds beta epsilon 0 0 0 else (1/0,1/0)) finalSdss allBetas cauchyBs

  let laplaceDeltas = zipWith4 (\sds beta b eps -> if beta == 0 then 0 else 2*exp(eps-1-(eps-b)/beta)) finalSdss allBetas laplaceBs laplaceEpsilons
  let laplaceError = combinedErrs finalQrs laplaceBs finalSdss
  let laplaceNoise = combinedEtas laplaceBs finalSdss

  -- if there are different (eps,delta) for several outputs, we show the minimal of them to the user for short representation
  let laplaceDelta   = foldr min (1/0) laplaceDeltas
  let laplaceEpsilon = foldr min (1/0) laplaceEpsilons

  traceIOIfDebug debug ("betas: " ++ show allBetas)
  traceIOIfDebug debug ("Cauchy bs: " ++ show cauchyBs)
  traceIOIfDebug debug ("laplace bs: " ++ show laplaceBs)
  traceIOIfDebug debug ("laplace deltas: " ++ show laplaceDeltas)
  traceIOIfDebug debug ("laplace epsilons: " ++ show laplaceEpsilons)
  traceIOIfDebug debug ("laplace alphas: " ++ show (map (\eps -> epsilon - eps) laplaceEpsilons))
  traceIOIfDebug debug ("Cauchy epsilon: " ++ show epsilon)
  traceIOIfDebug debug ("(1 - delta/chi): " ++ show (zipWith3 (\delta sds b -> 1.0 - 2 * sds * delta / b) laplaceDeltas finalSdss laplaceBs))

  let errorUB = errorUBprob args
  let noiseScaleCauchy  = find_noise_range_window cauchy_integral errorUB 1
  let noiseScaleLaplace = find_noise_range_window laplace_integral errorUB 1

  traceIOIfDebug debug ("cauchy scaling: " ++ show noiseScaleCauchy)
  traceIOIfDebug debug ("laplace scaling: " ++ show noiseScaleLaplace)


  -- analyser output
  traceIOIfDebug debug ("===============================")
  let outputList = [("actual outputs y: ",           show (map niceRound finalQrs)),
                    (show (round $ errorUB * 100) ++ "%-noise magnitude a: ",   show (map (niceRound . (* noiseScaleCauchy)) cauchyNoise)),
                    (show (round $ errorUB * 100) ++ "%-realtive error |a|/|y|: ", show (niceRound (cauchyError * noiseScaleCauchy * 100.0)) ++ "%"),
                    ("Cauchy (default) distribution: ",  "add noise a*z, where z ~ sqrt(2) / pi * 1 / (1 + |x|^4)"),
                    ("prior (worst instance): ", show (niceRound pr_pre) ++ "%"),
                    ("posterior (worst instance): ", show (niceRound pr_post) ++ "%"),
                    ("DP epsilon: ",                 show (niceRound epsilon)),
                    ("smoothness beta: ",            show (niceRound finalBeta)),
                    ("(epsilon,delta) for Laplace: ", "(" ++ show (niceRound laplaceEpsilon) ++
                                                      "," ++ show (niceRound laplaceDelta) ++ ")"),
                    ("norm N: ",                      niceNormPrint norm),
                    ("beta-smooth sensitivity w.r.t. N: ",  show (map niceRound finalSdss)),
                    (show (round $ errorUB * 100) ++ "%-noise magnitude a (Laplace): ",
                                                     show (map (niceRound . (* noiseScaleLaplace)) laplaceNoise)),
                    (show (round $ errorUB * 100) ++ "%-realtive error |a|/|y| (Laplace): ",
                                                     show (niceRound (laplaceError * 100.0 * noiseScaleLaplace)) ++ "%"),
                    ("Laplace noise distribution: ", "add noise a*z, where z ~ 1 / 2 * exp(-x)")]

  let sep = if alternative args then [B.unitSeparator2] else "\n"
  let out = if alternative args then map snd outputList else map (\(x,y) -> x ++ y) outputList
  putStrLn $ intercalate sep out


-- TODO it seems that we can remove sds (and maybe something else) since this is already a part of qmap
findBestBeta :: ProgramOptions -> String -> Double -> Maybe Double -> String -> String -> String -> [String] -> Int -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [BQ.DataWrtTable] -> AttMap -> [Int] -> IO (Double, M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double, [Double])
findBestBeta args outputTableName epsilon fixedBeta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap tableExprData attMap colTableCounts = do

  let step = performAnalysisBetaStep args outputTableName epsilon dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap [] tableExprData attMap [] colTableCounts
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

performAnalysisBetaStep :: ProgramOptions -> String -> Double -> String -> String -> String -> [String] -> Int -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> AttMap -> [(String, Maybe Double)] -> [Int] -> Maybe Double -> IO (M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double, [Double])
performAnalysisBetaStep args outputTableName epsilon dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts beta = do

  (qmap,taskAggrMap) <- performAnalysis args epsilon beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts
  let (qrs, bs, sdss) = unzip3 $ map (\key -> extractFinalResult (qmap ! key) (taskAggrMap ! key) B.resultForAllTables outputTableName) (M.keys qmap)
  let err = combinedErrs qrs bs sdss

  return (qmap,taskAggrMap,err,sdss)


performAnalysis :: ProgramOptions -> Double -> Maybe Double -> String -> String -> String -> [String] -> Int -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> AttMap -> [(String, Maybe Double)] -> [Int] -> IO (M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])])
performAnalysis args epsilon beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

  (qmap,taskAggrMap') <- BQ.performAnalyses args epsilon beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts

  -- if we choose beta that is not compatible with epsilon during optimization, we get a negative b, so we set it to 0 to get Infinity relative error
  -- in policy analysis, this means that desired epsilon, and hence the guessing advantage bound, could not be achieved
  let taskAggrMap = M.fromList $ map (\(key,taskAggrGroup) -> (key, map (\(taskName,res) -> (taskName, map (\ (tableName, (b,sds)) -> (tableName, (max b 0, sds)) ) res)) taskAggrGroup)) (M.toList taskAggrMap')
  return (qmap, taskAggrMap)

-- brute force search on b works well
findOptimalB :: Double -> Double -> Double -> Double -> Double -> Double -> (Double,Double)
findOptimalB sds beta eps alpha bestEps bestB =

    if alpha > eps then (bestEps, bestB) else
    let newEps = eps - alpha in
    let b = findOptimalB2 sds beta newEps alpha 0 0 in
    let (newEps',b') = if (b > bestB) && (b + beta <= newEps) then (newEps, b) else (bestEps, bestB) in
    --trace ("A: " ++ show ((alpha,b,1 - exp(-alpha), 4 * sds * exp(newEps-1-((newEps-b)/beta)) / b))) $
    findOptimalB sds beta eps (alpha+(eps / 100)) newEps' b'

findOptimalB2 :: Double -> Double -> Double -> Double -> Double -> Double -> Double
findOptimalB2 sds beta eps alpha b bestB =
    if b > eps - beta then bestB else
    let z  = 4 * sds * exp(eps-1-((eps-b)/beta)) / b in
    let b' = if (z >= 0) && (z <= 1 - exp(-alpha)) then b else bestB in
    --trace ("    B: " ++ show ((b,beta,eps,1 - exp(-alpha), z))) $
    findOptimalB2 sds beta eps alpha (b+((eps - beta) / 100)) b'

allCombsOfLists [] = [[]]
allCombsOfLists (xs:xss) =
    [(y:ys) | y <- xs, ys <- allCombsOfLists xss]

allCombsOfMaybeLists :: [Maybe [a]] -> [[Maybe a]]
allCombsOfMaybeLists [] = [[]]
allCombsOfMaybeLists (xs:xss) =
    concat [z | ys <- allCombsOfMaybeLists xss, let z = case xs of {Nothing -> [(Nothing : ys)]; _ -> [((Just y) : ys) | y <- (fromJust xs)]}]
