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
import DatabaseQ
import PolicyQ
import GroupQ
import AexprQ

traceIOIfDebug :: Bool -> String -> IO ()
traceIOIfDebug debug msg = do
    if debug then traceIO msg
    else return ()


-- this is used only for nice output printing
data Result = Result {sensitivity :: String, query_result :: String, cauchy_noise :: String, cauchy_relative_err :: String,
              beta :: String, delta :: String, laplace_noise :: String, laplace_relative_err :: String, norm :: String} deriving (Data, G.Generic, Show)

constructResult [v2,v3,v4,v5,v6,v7,v8,v9,v10] = Result {sensitivity = v2,
                                                query_result = v3,
                                                cauchy_noise = v4,
                                                cauchy_relative_err = v5,
                                                beta = v6,
                                                delta = v7,
                                                laplace_noise = v8,
                                                laplace_relative_err = v9,
                                                norm = v10}

-- number of steps in optimization
numOfSearchSteps = fromIntegral 100

-- nice printing
niceRound x = fromIntegral (round (x * 1000)) / 1000
printFloatL = printf "%0.6f"
printFloatS = printf "%0.2f"
printFloatE = (\x -> showEFloat (Just 2) x "")

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

-- given max-distance d, aimed guessing advantage bound ga, and probailities p, q, compute epsilon
compute_epsilon :: Bool -> Double -> Double -> Double -> Double -> Double
compute_epsilon _ _ 1 1 _ = 1/0
compute_epsilon pos ga' q p d =

    -- we know that the probability cannot grow above 100%
    if pos then
        let ga = min (1 - p) ga' in
        let z = p / (q - p) * (1 / (ga + p) - 1) in
        --trace ("eps1: " ++ show p ++ " " ++ show q ++ " " ++ show ga ++ " " ++ show z ++ " " ++ show (- (log z) / d)) $
        - (log z) / d
    else
        let ga = min p ga' in
        let z = (q - p) / p * (q / (ga + (1 - p) - (1 - q)) - 1) in
        --trace ("eps0: " ++ show p ++ " " ++ show q ++ " " ++ show ga ++ " " ++ show z ++ " " ++ show (- (log z) / d)) $
        - (log z) / d

compute_worst_epsilon :: Double -> Double -> Double -> Double
compute_worst_epsilon ga q d =
    (2 / d) * (log ((sqrt q + sqrt (ga*(ga + q - 1))) / (1 - ga)))

-- given a bounding box with side length a, compute the epsilon required to hide a unit box there
compute_eps_for_a :: Bool -> Double -> Int -> M.Map String [Either Double String] -> [(Int, M.Map [String] PlcData)] -> Double -> Int -> (Double,Double,Double,Double)
compute_eps_for_a pos ga numOfRows xmap expr sample_a nq =

    -- compute the weight of X' (distributions of some dimensions can be unknown)
    -- if different elements come with different probabilities, we consider all combinations
    --trace ("xmap: " ++ show xmap) $
    --trace ("expr: " ++ show expr) $
    let qssAs = map (\(s,m) -> let (vss,ass) = unzip $ map (\varNames ->

                                    -- adjust proposed sample_a to the actual bounds R
                                    -- the returned list 'as' is the list of max-distances
                                    let (PlcData b ur r rr d g) = m ! varNames in
                                    let xss = map (xmap !) varNames in

                                    -- non-sensitive dimensions do not change anything
                                    if not b then
                                        unzip $ replicate numOfRows (1.0, 1.0)
                                    else
                                        -- this 'aa' defines the probability area, and not the distance
                                        let aa = if d then rr
                                                else max r $ min rr sample_a
                                        in unzip $ map (\xs -> case g xs (ur * aa) of
                                                          Nothing   -> (1.0, if d then 1.0 else 2.0*rr)
                                                          Just (v,a)-> (v,a)) xss
                                    ) (M.keys m)
                               in
                                    (map (((fromIntegral s) * ) . product) (transpose vss), foldr max 1.0 (concat ass))) expr
    in

    let pss'  = map (\(s,m) -> let vss = map (\varNames ->

                                    let (PlcData b ur r _ _ g) = m ! varNames in
                                    let xss = map (xmap !) varNames in

                                    if not b then
                                         Just $ replicate numOfRows 1.0
                                    else
                                         let vs = map (\xs -> case g xs (ur * r) of
                                                          Nothing   -> Nothing
                                                          Just (v,a)-> Just v) xss
                                         in (if elem Nothing vs then Nothing else Just (map fromJust vs))
                                    ) (M.keys m)
                               in
                                    if elem Nothing vss then replicate numOfRows Nothing
                                    else
                                        let wss = transpose $ (map fromJust) vss in
                                        map ((Just . ((fromIntegral s) *) . product) ) wss) expr
    in

    -- determine the unique bound 'a' that is true for all dimensions
    let (qss',as) = unzip qssAs in
    let a = foldr max 1 as in
    let d = a * fromIntegral nq in

    let pss = transpose pss' in
    let qss = transpose qss' in

    --trace (show sample_a)
    --trace ("pss: " ++ show pss) $
    --trace ("qss: " ++ show qss) $

    -- compute the epsilon (use worst-case p if p is unknown)
    let results = zipWith (\ps qs ->
                       let q = sum qs in
                       if elem Nothing ps then
                               let eps = compute_worst_epsilon ga q d in
                               let p = min q ((sqrt q) * ((exp (d * eps / 2)) - (sqrt q)) / ((exp (d * eps)) - 1)) in
                               (a,eps,q,p)
                       else
                               let p = sum (map fromJust ps) in
                               let eps = compute_epsilon pos ga q p d in
                               (a,eps,q,p)
                  ) pss qss
    in

    -- if there are many possible values of p in the given set of sensitive rows, then choose the worst one
    let (a,epsilon,q,p) = foldr (\x1@(_,e1,_,_) x2@(_,e2,_,_) -> if isNaN e2 || e1 < e2 then x1 else x2) (head results) (tail results) in
    (a,epsilon,q,p)


optimal_a_epsilon :: Bool -> Double -> Int -> M.Map String [Either Double String] -> Double -> Double -> [(Int, M.Map [String] PlcData)] -> Double -> Double -> Double -> Double
                     -> Double -> Double -> Int -> (Double,Double,Double,Double)
optimal_a_epsilon _ _ _ _ _ _ _ a epsilon q p 0 _ _ = (a,epsilon,q,p)
optimal_a_epsilon pos ga numOfRows xmap scaled_r scaled_rr expr a epsilon q p k n nq =

    -- compute the sample value for a and check how good it is
    let sample_a = scaled_r + k * (scaled_rr - scaled_r) / n in
    let (a',epsilon',q',p') = compute_eps_for_a pos ga numOfRows xmap expr sample_a nq in

    --take the best values found so far
    let (a'',epsilon'',q'',p'') = if isNaN epsilon || epsilon' > epsilon then (a',epsilon',q',p') else (a,epsilon,q,p) in
    optimal_a_epsilon pos ga numOfRows xmap scaled_r scaled_rr expr a'' epsilon'' q'' p'' (k-1) n nq


performDPAnalysis :: ProgramOptions -> String -> String -> String -> String -> [String] -> Int -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> AttMap -> [(String, Maybe Double)] -> [Int] -> IO ()
performDPAnalysis args outputTableName dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

  let debug    = not (alternative args)
  let epsilon' = getEpsilon args
  let beta     = getBeta args
  let delta    = getDelta args

  -- do not look for optimal beta if it has been specified by the user
  (qmap,taskAggrMap) <- case beta of
          Just _  -> performAnalysis args False epsilon' beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts
          Nothing -> do
                         (_,q,tm,_) <- findOptimalBeta args outputTableName epsilon' beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts
                         return (q,tm)

  -- if we have a GroupBy query, we need to scale epsilon accordingly
  let epsilon = epsilon' / (fromIntegral numOfOutputs)

  traceIOIfDebug debug ("===============================")
  traceIOIfDebug debug ("final qmap: " ++ (show qmap))
  traceIOIfDebug debug ("final taskAggr: " ++ (show taskAggrMap))

  -- if a group is empty, we set its output to 0
  -- TODO think how to define for MIN/MAX queries in a better way
  let outMap = M.fromListWith (++) $ concat $ map (\key -> extractFinalResults (if M.member key qmap then qmap ! key else 0) (taskAggrMap ! key) key) (M.keys taskAggrMap)
  let outList = map (\((taskName,tableName), zs) -> (taskName,[(tableName,zs)])) $ M.toList outMap
  let taskList = M.toList $ M.fromListWith (++) outList

  let sep1 = if alternative args then [B.unitSeparator] else "\n"
  let sep2 = if alternative args then [B.unitSeparator2] else "\n\n"
  let sep3 = if alternative args then [B.unitSeparator3] else "\t"

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
          let tableResultMap = M.fromList $ map (\(v : vs) -> (v, constructResult vs)) tableMap
          when debug $ T.printTable tableResultMap
  putStr ""


performPolicyAnalysis :: ProgramOptions -> String -> String -> String -> String -> [String] ->Int -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> PlcCostType -> AttMap -> [Int] -> IO ()
performPolicyAnalysis args outputTableName dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData plcCostType attMap colTableCounts = do

  -- the input epsilon now works as GA, the upper bound on attacker's advantage
  let debug = not (alternative args)
  let ga = getEpsilon args
  let fixedBeta = getBeta args

  -- this basically scales epsilon nq times, assuming that up to nq queries may be run on the same data
  -- we actually have numOfOutputs as well, but that will be taken into account by Banach analyser
  let nq = numOfQueries args

  -- extract the sensitive expression and the variables used within it
  let plcExpr = getStatement plcCostType
  let allSensVars = extract_vars plcExpr
  let sensVarList = nub $ concat allSensVars

  -- construct the query that reads sensitive data from source tables
  let plcFilterMap = M.fromList $ getFilters plcCostType
  let sensTableNames = M.keys plcFilterMap

  let selStr   = intercalate ", " sensVarList
  let fromStr  = intercalate ", " sensTableNames
  let whereStr = intercalate " AND " $ map (\tn -> let prefix = tn ++ [tsep] in
                                                   aexprToString $ updatePreficesAexpr (S.fromList sensTableNames) prefix (plcFilterMap ! tn)
                                            ) (M.keys plcFilterMap)
  let dataQuery = "SELECT " ++ selStr ++ " FROM " ++ fromStr ++ " WHERE " ++ whereStr ++ ";"

  -- process the policy and the attacker knowledge
  let plainTypeMaps = map (\(tname,tmap) -> map (\(x,y) -> (preficedVarName tname x,y)) tmap) typeMap
  let plainTypeMap  = M.fromList $ concat plainTypeMaps

  -- extract the actual data (we will need it to compute priors)
  results <- sendQueryToDb args dataQuery
  let numOfRows = length results
  let xmap = M.fromList $ zipWith (\var rs -> if plainTypeMap ! var == "text" then
                                                  (var, map (Right . sqlToString) rs)
                                              else
                                                  (var, map (Left . sqlToDouble) rs) ) sensVarList (transpose results)

  traceIOIfDebug debug ("type map: " ++ show plainTypeMap)
  traceIOIfDebug debug ("data query: " ++ show dataQuery)
  --traceIOIfDebug debug ("xmap: " ++ show xmap)

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


  -- compute p and q using the equalities and P(A || B) = P(A) + P(B) - P(AB), P(AA) = P(A), P(AB) = P(A)*P(B)
  let pqExpr = computePweights plcExprExt

  -- it seems that brute-forcing optimal epsilon and a works quite well
  -- we consider multidimensional space, where the radius is linf-norm
  let num_of_tries = 10000

  -- since 'a' is only an estimation parameter, we find the noise separately for the positive and the negative guess, and then take the largest noise
  let (init_a, init_epsilon, init_q, init_p) = compute_eps_for_a True ga numOfRows xmap pqExpr scaled_rr nq
  let (a1,epsilon1,q1,p1) = if ga == 0 then (init_a, init_epsilon, init_q, init_p) else optimal_a_epsilon True ga numOfRows xmap scaled_r scaled_rr pqExpr init_a init_epsilon init_q init_p numOfSearchSteps numOfSearchSteps nq

  let (init_a, init_epsilon, init_q, init_p) = compute_eps_for_a False ga numOfRows xmap pqExpr scaled_rr nq
  let (a0,epsilon0,q0,p0) = if ga == 0 then (init_a, init_epsilon, init_q, init_p) else optimal_a_epsilon False ga numOfRows xmap scaled_r scaled_rr pqExpr init_a init_epsilon init_q init_p numOfSearchSteps numOfSearchSteps nq

  let (a,epsilon',q,p) = if epsilon0 < epsilon1 then (a0,epsilon0,1-q0,1-p0) else (a1,epsilon1,q1,p1)

  traceIOIfDebug debug ("plcExpr: " ++ show plcExpr)
  traceIOIfDebug debug ("plcExprExt: " ++ show plcExprExt)
  traceIOIfDebug debug ("pqExpr: " ++ show pqExpr)
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

  --error "STOP"
  let pr_pre  = p1 * 100
  let pr_post = 1 / (1 + exp(- a1 * epsilon1 * (fromIntegral nq)) * (q1-p1) / p1) * 100

  -- the following output is more informative, but less understandable
  -- if ga < prior, then the lower bound may be negative, and we take the bound 0 in this case
  --let pr_post = [max 0 (q0 - 1 / (1 + exp(- a0 * epsilon0 * (fromIntegral nq)) * p0 / (q0-p0))) * 100, 1 / (1 + exp(- a1 * epsilon1 * (fromIntegral nq)) * (q1-p1) / p1) * 100]

  (finalBeta,qmap,taskAggrMap,cauchyError) <- findOptimalBeta args outputTableName epsilon' fixedBeta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap [] colTableCounts

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


findOptimalBeta :: ProgramOptions -> String -> Double -> Maybe Double -> String -> String -> String -> [String] -> Int -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> AttMap -> [(String, Maybe Double)] -> [Int] -> IO (Double, M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double)
findOptimalBeta args outputTableName epsilon fixedBeta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

    -- define the function that we will optimize
    let step = performAnalysisBetaStep args outputTableName epsilon dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts

    -- take fixedBeta if it is defined, and optimize otherwise
    (finalBeta,finalQmap,finaltaskAggr,finalError) <- case fixedBeta of
                    Nothing -> do
                        initialBeta' <- BQ.findMinimumBeta args False epsilon Nothing dataPath separator initialQuery colNames typeMap sensitiveVarList tableExprData attMap tableGs colTableCounts
                        -- we cannot use beta=0 for combined sensitivity, as it would result in an infinite loop
                        let betaMax = epsilon / 5.0
                        let betaMin = 0
                        let unit = betaMax / numOfSearchSteps
                        let initialBeta = if combinedSens args && initialBeta' == 0 then unit else initialBeta'
                        (initialQmap,initialTaskAggr,initialError) <- step False (Just initialBeta)
                        findOptimalBeta2 unit step betaMin betaMax initialBeta initialQmap initialTaskAggr initialError
                    Just beta' -> do
                        (qmap',taskAggr',err') <- step False (Just beta')
                        return (beta', qmap',taskAggr', err')
    return (finalBeta,finalQmap,finaltaskAggr,finalError)

-- binary search on beta
findOptimalBeta2 :: Double -> (Bool -> Maybe Double -> IO (M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])],Double)) -> Double -> Double -> Double -> M.Map [String] Double -> M.Map [String] [(String, [(String, (Double, Double))])] -> Double -> IO (Double, M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double)
findOptimalBeta2 unit step betaMin betaMax bestBeta bestQmap bestTaskAggr bestError =

    if abs(betaMax - betaMin) <= unit || (betaMax == 1/0) then do
        return (bestBeta, bestQmap, bestTaskAggr, bestError)
    else do
        let betaU = (betaMin + betaMax + unit) / 2.0
        let betaL = (betaMin + betaMax - unit) / 2.0
        (qmapU, taskAggrU, errU) <- step True (Just betaU)
        (qmapL, taskAggrL, errL) <- step True (Just betaL)
        let (beta, qmap, taskAggr, err, betaMin',betaMax') = if errU < errL then (betaU, qmapU, taskAggrU, errU, betaU, betaMax) else (betaL, qmapL, taskAggrL, errL, betaMin, betaL)
        let (beta', qmap', taskAggr', err') = if err < bestError then (beta, qmap, taskAggr, err) else (bestBeta, bestQmap, bestTaskAggr, bestError)
        findOptimalBeta2 unit step betaMin' betaMax' beta' qmap' taskAggr' err'


-- linear search on beta (experimental, currently not used)
-- remember that we need to start from beta > 0 in CS analysis
findOptimalBetaL :: (Bool -> Maybe Double -> IO (M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])],Double)) -> Double -> Double -> Double -> M.Map [String] Double -> M.Map [String] [(String, [(String, (Double, Double))])] -> Double -> IO (Double, M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double)
findOptimalBetaL step beta betaMax bestBeta bestQmap bestTaskAggr bestError =

    if (beta > betaMax) || (betaMax == 1/0) then do
        return (bestBeta, bestQmap, bestTaskAggr, bestError)
    else do
        (qmap, taskAggr, err) <- step True (Just beta)
        let (beta', qmap', taskAggr', err') = if err < bestError then (beta, qmap, taskAggr, err) else (bestBeta, bestQmap, bestTaskAggr, bestError)
        findOptimalBetaL step (beta+(betaMax / numOfSearchSteps)) betaMax beta' qmap' taskAggr' err'


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

performAnalysisBetaStep :: ProgramOptions -> String -> Double -> String -> String -> String -> [String] -> Int -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> AttMap -> [(String, Maybe Double)] -> [Int] -> Bool -> Maybe Double -> IO (M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double)
performAnalysisBetaStep args outputTableName epsilon dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts silent beta = do

  (qmap,taskAggrMap) <- performAnalysis args silent epsilon beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts
  let (qrs, bs, sdss) = unzip3 $ map (\key -> extractFinalResult (qmap ! key) (taskAggrMap ! key) B.resultForAllTables outputTableName) (M.keys qmap)
  let err = combinedErrs qrs bs sdss

  return (qmap,taskAggrMap,err)


performAnalysis :: ProgramOptions -> Bool -> Double -> Maybe Double -> String -> String -> String -> [String] -> Int -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> AttMap -> [(String, Maybe Double)] -> [Int] -> IO (M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])])
performAnalysis args silent epsilon beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

  (qmap,taskAggrMap',_) <- BQ.performAnalyses args silent epsilon beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts

  -- if we choose beta that is not compatible with epsilon during optimization, we get a negative b, so we set it to 0 to get Infinity relative error
  -- in policy analysis, this means that desired epsilon, and hence the guessing advantage bound, could not be achieved
  let taskAggrMap = M.fromList $ map (\(key,taskAggrGroup) -> (key, map (\(taskName,res) -> (taskName, map (\ (tableName, (b,sds)) -> (tableName, (max b 0, sds)) ) res)) taskAggrGroup)) (M.toList taskAggrMap')
  return (qmap, taskAggrMap)

-- brute force search on b works well
findOptimalB :: Double -> Double -> Double -> Double -> Double -> Double -> (Double,Double)
findOptimalB sds beta eps alpha bestEps bestB =

    if (eps == 0) || (alpha > eps) then (bestEps, bestB) else
    let newEps = eps - alpha in
    let b = findOptimalB2 sds beta newEps alpha 0 0 in
    let (newEps',b') = if (b > bestB) && (b + beta <= newEps) then (newEps, b) else (bestEps, bestB) in
    --trace ("A: " ++ show ((alpha,b,1 - exp(-alpha), 4 * sds * exp(newEps-1-((newEps-b)/beta)) / b))) $
    findOptimalB sds beta eps (alpha+(eps / numOfSearchSteps)) newEps' b'

findOptimalB2 :: Double -> Double -> Double -> Double -> Double -> Double -> Double
findOptimalB2 sds beta eps alpha b bestB =
    if (eps - beta) == 0 || (b > eps - beta) then bestB else
    let z  = 4 * sds * exp(eps-1-((eps-b)/beta)) / b in
    let b' = if (z >= 0) && (z <= 1 - exp(-alpha)) then b else bestB in
    --trace ("    B: " ++ show ((b,beta,eps,1 - exp(-alpha), z))) $
    findOptimalB2 sds beta eps alpha (b+((eps - beta) / numOfSearchSteps)) b'

allCombsOfLists [] = [[]]
allCombsOfLists (xs:xss) =
    [(y:ys) | y <- xs, ys <- allCombsOfLists xss]

allCombsOfMaybeLists :: [Maybe [a]] -> [[Maybe a]]
allCombsOfMaybeLists [] = [[]]
allCombsOfMaybeLists (xs:xss) =
    concat [z | ys <- allCombsOfMaybeLists xss, let z = case xs of {Nothing -> [(Nothing : ys)]; _ -> [((Just y) : ys) | y <- (fromJust xs)]}]
