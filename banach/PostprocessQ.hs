module PostprocessQ where

import Debug.Trace

import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import ProgramOptions
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

filterWith [] [] = []
filterWith (b:bs) (x:xs) =
    let ys = filterWith bs xs in
    if b then (x:ys) else ys

-- finds y such that y * exp(y) = x
lambert x 0 = 1
lambert x n =
    let an = lambert x (n - 1) in
    an - (an * exp(an) - x) / ((an + 1) * exp(an))

optimal_a_epsilon :: Double -> Double -> Double -> Double -> Double -> Double -> Double -> Double -> Double -> (Double,Double)
optimal_a_epsilon _ _ _ _  a epsilon 0 _ _ = (a,epsilon)
optimal_a_epsilon xWeight c r rr a epsilon k n m =

    let a' = r + k * (rr - r) / n in
    let xbarWeight = a'**m - xWeight in
    let epsilon' = log ((xbarWeight / xWeight) / c) / a' in

    let (a'',epsilon'') = if (epsilon' > epsilon) then (a',epsilon') else (a,epsilon) in
    optimal_a_epsilon xWeight c r rr a'' epsilon'' (k-1) n m

performDPAnalysis :: ProgramOptions -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [String] -> [(String, String, OneGroupData, B.TableExpr, (String,String,String))] -> M.Map String VarState -> [(String, Maybe Double)] -> [Int] -> IO ()
performDPAnalysis args dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do


  let epsilon = getEpsilon args
  let beta    = getBeta args
  (qr,taskAggr) <- performAnalysis args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts
  let taskStr = if alternative args then
          map (\(taskName,res) -> taskName ++ [B.unitSeparator] ++
                  (intercalate [B.unitSeparator] $ concat $ map (\ (tableName, (b,sds)) -> [tableName, show sds, show qr, show (sds/b), show ((sds/b) / qr * 100)]) res)) taskAggr
      else
          map (\(taskName,res) -> taskName ++ "\n" ++
                  (intercalate "\n" $ map (\ (tableName, (b,sds)) -> printf "%s: %0.6f\t %0.6f\t %0.6f\t %0.3f" tableName sds qr (sds/b) ((sds/b) / qr * 100)) res)) taskAggr
  putStrLn $ intercalate (if alternative args then [B.unitSeparator2] else "\n\n") taskStr

-- TODO continue from here, add special processing of sensRows
performPolicyAnalysis :: ProgramOptions -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [(String, String, OneGroupData, B.TableExpr, (String,String,String))] -> [(M.Map String VarState, Double)] -> M.Map String VarState -> [Int] -> IO ()
performPolicyAnalysis args dataPath separator initialQuery colNames typeMap taskMap tableExprData plcMaps attMap colTableCounts = do

  -- the input epsilon now works as delta, the upper bound on attacker's advantage
  let debug = not (alternative args)
  let delta = getEpsilon args
  let fixedBeta = getBeta args

  -- process the policy and the attacker knowledge
  let plainTypeMaps = map (\(tname,tmap) -> map (\(x,y) -> (tname ++ [tsep] ++ x,y)) tmap) typeMap
  let plainTypeMap  = M.fromList $ concat plainTypeMaps

  -- TODO this is not the right way to compute cost for several sensitive sets
  let cost = sum $ map snd plcMaps

  --remove the special variables that are not needed
  let kwlen = length reservedSensRowsKeyword
  let plcMapData = map (M.filterWithKey (\varName _ -> length varName < kwlen || reverse (take kwlen (reverse varName)) /= reservedSensRowsKeyword) . fst) plcMaps

  let bss  = map (extract_bs attMap) plcMapData
  let rss    = zipWith filterWith bss $ map (extract_rs attMap) plcMapData
  let css    = zipWith filterWith bss $ map (extract_crs attMap) plcMapData
  let bounds = zipWith filterWith bss $ map (extract_Rs attMap plainTypeMap) plcMapData

  let rrss'  = map (map (\(lb,ub) -> (ub - lb) / 2.0)) bounds
  let crss'  = zipWith filterWith bss $ map (extract_CRs attMap plainTypeMap) plcMapData

  let rrss = zipWith (zipWith (/)) rrss' rss --rescaled bounds
  let crss = zipWith (zipWith (/)) crss' css --rescaled counts

  -- the weights of separate blocks in the sensitive area
  let pss  = map (map (\cr -> if cr == 0 then 1.0 else 1 / cr)) crss

  -- space dimensionality comes from the total number of sensitive variables
  -- we multiply the dimensions of variables belonging to one sensitive set
  -- we add the weights of different sensitive sets, since the attacker may guess any of them
  -- TODO do not include repeating variables muliple times into m and the intersection weight
  let allSensVars = S.fromList $ concat (map M.keys plcMapData) 

  let m = fromIntegral $ length (concat rss)
  let intersectionWeight = product $ map product pss

  let total = 1 / intersectionWeight -- how much choices the are in total if we take X' as a unit
  let p = (sum $ map product pss) - (fromIntegral (length pss - 1)) * intersectionWeight
  let xWeight = p * total

  -- we know that the probability cannot grow above 100%
  let d = min (1 - p) delta
  -- we consider multidimensional space, where the radius is linf-norm
  let ub = p + d

  -- it seems that brute-forcing optimal epsilon and a works quite well
  let c = (ub**(-1) - 1)
  let rr = foldr max 0 (concat rrss)
  let init_epsilon = log ((rr**m - 1**m) * (1 / xWeight) * c) / rr
  let num_of_tries = 10000
  let (a',epsilon') = optimal_a_epsilon xWeight c 1 rr rr init_epsilon num_of_tries num_of_tries m

  -- convert guessing probability to epsilon (assuming that 'a' is optimal)
  -- let es' = map (\r -> (lambert (ub / (exp(1) * (1 - ub))) 10) / r) rs
  -- consider scaled dimensions, where r = 1 for all r
  --let epsilon' = if m == 1 then lambert (ub / (exp(1) * (1 - ub))) 10 else m / (exp(1) * (1 / ub - 1 + exp(-m)) ** (1 / m))

  -- find the initial (optimal) value of a
  -- we compute a = m / epsilon + 1 if m = 1, and m / epsilon for the multidimensional case
  --let a' = if m == 1 then m / epsilon' + 1 else m / epsilon'

  traceIOIfDebug debug ("plcMaps: " ++ show plcMaps)
  traceIOIfDebug debug ("allSensVars: " ++ show allSensVars)
  traceIOIfDebug debug ("m: " ++ (show m))
  traceIOIfDebug debug ("pss: " ++ (show pss))
  traceIOIfDebug debug ("p: " ++ (show p))
  traceIOIfDebug debug ("total: " ++ (show total))
  traceIOIfDebug debug ("d: " ++ (show d))
  traceIOIfDebug debug ("a': " ++ (show a'))
  traceIOIfDebug debug ("rss: " ++ (show rss))
  traceIOIfDebug debug ("css: " ++ (show css))
  traceIOIfDebug debug ("rrss: " ++ (show rrss'))
  traceIOIfDebug debug ("crss: " ++ (show crss'))
  traceIOIfDebug debug ("eps': " ++ (show epsilon'))

  -- in the case a > rr for some rr, set a = rr
  let ass = map (map (\rr -> min rr a')) rrss
  let a = foldr max 0 (concat ass)

  -- TODO use some better detection of discrete choice than a = 1.0 here
  let xbarWeight = if a == 1.0 then total - xWeight else (product $ map product ass) - xWeight

  -- recompute a and the epsilon
  let epsilon = log ((xbarWeight / xWeight) / c) / a
  traceIOIfDebug debug ("a: " ++ (show a))
  traceIOIfDebug debug ("x: " ++ (show xWeight))
  traceIOIfDebug debug ("xbar: " ++ (show xbarWeight))
  traceIOIfDebug debug ("eps: " ++ (show epsilon))
  traceIOIfDebug debug ("beta: " ++ (show fixedBeta))

  let pr_pre  = p
  let pr_post = 1 / (1 + exp(- a * epsilon) * (xbarWeight / xWeight))

  --traceIO ("Pr_pre: " ++ (show ps) ++ "  -->  " ++ (show pr_pre))
  --traceIO ("Pr_post: " ++ (show posts) ++ "  -->  " ++ (show pr_post))

  let step = performAnalysisBetaStep args epsilon dataPath separator initialQuery colNames typeMap taskMap [] tableExprData attMap [] colTableCounts
  (finalBeta,finalError) <- case fixedBeta of
                    Nothing -> do
                        initialBeta <- BQ.findMinimumBeta args epsilon Nothing dataPath separator initialQuery colNames typeMap taskMap [] tableExprData attMap [] colTableCounts
                        initialError <- step (Just initialBeta)
                        repeatUntilGetBestError step initialError initialBeta (epsilon / 5.0) initialBeta initialError
                    Just beta' -> do
                        err' <- step (Just beta')
                        return (beta', err')
  
  let expectedCost = delta * cost
  traceIOIfDebug debug ("params: beta=" ++ (show finalBeta) ++ ", eps=" ++ (show epsilon))

  --putStrLn $ intercalate ("\n") [show (pr_pre * 100.0), show (pr_post * 100.0), show expectedCost, show finalError]
  putStrLn $ intercalate (if alternative args then [B.unitSeparator2] else "\n\n") [show (pr_pre * 100.0), show (pr_post * 100.0), show expectedCost, show (finalError * 100)]
  -- for PRISMS graphs, we have modified the output, adjusting it to histograms
  -- putStrLn $ intercalate (if alternative args then ";" else "\n\n") [show delta, show finalError]


repeatUntilGetBestError :: (Maybe Double -> IO Double) -> Double -> Double -> Double -> Double -> Double -> IO (Double,Double)
repeatUntilGetBestError step prevError betaMin betaMax bestBeta bestError = do
    let nextBeta = (betaMax + betaMin) / 2.0
    nextError <- step (Just nextBeta)
    let (bestBeta', bestError') = if nextError < bestError then (nextBeta, nextError) else (bestBeta, bestError)
    if (betaMax - betaMin > 0.01) && (betaMax > 0.01) && (betaMin /= 1/0) && (betaMax /= 1/0)
      then do
        --do binary search
        if (prevError <= nextError) then do
            repeatUntilGetBestError step prevError betaMin nextBeta bestBeta' bestError'
        else do
            repeatUntilGetBestError step nextError nextBeta betaMax bestBeta' bestError'
      else do
        return (bestBeta', bestError')

performAnalysisBetaStep :: ProgramOptions -> Double -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [String] -> [(String, String, OneGroupData, B.TableExpr, (String,String,String))] -> M.Map String VarState -> [(String, Maybe Double)] -> [Int] -> Maybe Double -> IO Double
performAnalysisBetaStep args epsilon dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts beta = do

  (qr,taskAggr) <- performAnalysis args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts
  let resultMap = M.fromList $ snd (last taskAggr)

  -- take the main results, which is "for all tables"
  let (b, sds) = resultMap ! B.resultForAllTables
  return ((sds / b) / qr)


performAnalysis :: ProgramOptions -> Double -> Maybe Double -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [String] -> [(String, String, OneGroupData, B.TableExpr, (String,String,String))] -> M.Map String VarState -> [(String, Maybe Double)] -> [Int] -> IO (Double,[(String, [(String, (Double, Double))])])
performAnalysis args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

  (qr,taskAggr') <- BQ.performAnalyses args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts

  -- if we choose beta that is not compatible with epsilon during optimization, we get a negative b, so we set it to 0 to get Infinity relative error
  -- in policy analysis, this means that desired epsilon, and hence the guessing advantage bound, could not be achieved
  let taskAggr = map (\(taskName,res) -> (taskName, map (\ (tableName, (b,sds)) -> (tableName, (max b 0, sds)) ) res)) taskAggr'
  return (qr, taskAggr)





