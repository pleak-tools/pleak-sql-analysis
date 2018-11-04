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

performDPAnalysis :: ProgramOptions -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [String] -> [(String, B.TableExpr, (String,String,String))] -> M.Map String VarState -> [(String, Maybe Double)] -> [Int] -> IO ()
performDPAnalysis args dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do


  let epsilon = getEpsilon args
  let beta    = getBeta args
  (qr,taskAggr) <- BQ.performAnalyses args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts
  let taskStr = if alternative args then
          map (\(taskName,res) -> taskName ++ [B.unitSeparator] ++
                  (intercalate [B.unitSeparator] $ concat $ map (\ (tableName, (b,sds)) -> [tableName, show sds, show qr, show (sds/b), show ((sds/b) / qr * 100)]) res)) taskAggr
      else
          map (\(taskName,res) -> taskName ++ "\n" ++
                  (intercalate "\n" $ map (\ (tableName, (b,sds)) -> printf "%s: %0.6f\t %0.6f\t %0.6f\t %0.3f" tableName sds qr (sds/b) ((sds/b) / qr * 100)) res)) taskAggr
  putStrLn $ intercalate (if alternative args then [B.unitSeparator2] else "\n\n") taskStr

performPolicyAnalysis :: ProgramOptions -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [(String, B.TableExpr, (String,String,String))] -> [(M.Map String VarState, Double)] -> M.Map String VarState -> [Int] -> IO ()
performPolicyAnalysis args dataPath separator initialQuery colNames typeMap taskMap tableExprData plcMaps attMap colTableCounts = do

  -- the input epsilon now works as delta, the upper bound on attacker's advantage
  let debug = not (alternative args)
  let delta = getEpsilon args
  let fixedBeta = getBeta args

  -- process the policy and the attacker knowledge
  let plainTypeMaps = map (\(tname,tmap) -> map (\(x,y) -> (tname ++ "." ++ x,y)) tmap) typeMap
  let plainTypeMap  = M.fromList $ concat plainTypeMaps

  let cost = sum $ map snd plcMaps

  let bss  = map (extract_bs attMap . fst) plcMaps
  let rss   = zipWith filterWith bss $ map (extract_rs attMap . fst) plcMaps
  let css   = zipWith filterWith bss $ map (extract_crs attMap . fst) plcMaps
  let rrss' = zipWith filterWith bss $ map (extract_Rs attMap plainTypeMap . fst) plcMaps
  let crss' = zipWith filterWith bss $ map (extract_CRs attMap plainTypeMap . fst) plcMaps

  let rrss = zipWith (zipWith (/)) rrss' rss --rescaled bounds
  let crss = zipWith (zipWith (/)) crss' css --rescaled counts

  -- the weights of separate blocks in the sensitive area
  let pss  = map (map (\cr -> if cr == 0 then 1.0 else 1 / cr)) crss

  -- space dimensionality comes from the total number of sensitive variables
  -- we multiply the dimensions of variables belonging to one sensitive set
  -- we add the weights of different sensitive sets, since the attacker may guess any of them
  -- TODO do not include repeating variables muliple times into m and the intersection weight
  let allSensVars = S.fromList $ concat (map (M.keys . fst) plcMaps) 

  let m = fromIntegral $ length (concat rss)
  let intersectionWeight = product $ map product pss

  let total = 1 / intersectionWeight -- how much choices the are in total if we take X' as a unit
  let p = (sum $ map product pss) - (fromIntegral (length pss - 1)) * intersectionWeight
  let xWeight = p * total

  -- we know that the probability cannot grow above 100%
  let d = min (1 - p) delta
  -- we consider multidimensional space, where the radius is linf-norm
  let ub = p + d

  -- convert guessing probability to epsilon (assuming that 'a' is optimal)
  -- let es' = map (\r -> (lambert (ub / (exp(1) * (1 - ub))) 10) / r) rs
  -- consider scaled dimensions, where r = 1 for all r
  let epsilon' = if m == 1 then lambert (ub / (exp(1) * (1 - ub))) 10 else m / (exp(1) * (1 / ub - 1 + exp(-m)) ** (1 / m))

  -- find the initial (optimal) value of a
  -- we compute a = m / epsilon + 1 if m = 1, and m / epsilon for the multidimensional case
  let a' = if m == 1 then m / epsilon' + 1 else m / epsilon'

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
  traceIOIfDebug debug ("rrss: " ++ (show rrss))
  traceIOIfDebug debug ("crss: " ++ (show crss))
  traceIOIfDebug debug ("eps': " ++ (show epsilon'))

  -- in the case a > rr for some rr, set a = rr
  let ass = map (map (\rr -> min rr a')) rrss
  let a = foldr max 0 (concat ass)

  -- TODO use some better detection of discrete choice than a = 1.0 here
  let xbarWeight = if a == 1.0 then total - xWeight else (sum $ map product ass) - xWeight

  -- recompute a and the epsilon
  let epsilon = log ((xbarWeight / xWeight) / (ub**(-1) - 1)) / a
  traceIOIfDebug debug ("a: " ++ (show a))
  traceIOIfDebug debug ("x: " ++ (show xWeight))
  traceIOIfDebug debug ("xbar: " ++ (show xbarWeight))
  traceIOIfDebug debug ("eps: " ++ (show epsilon))

  let pr_pre  = p
  let pr_post = 1 / (1 + exp(- a * epsilon) * (xbarWeight / xWeight))

  --traceIO ("Pr_pre: " ++ (show ps) ++ "  -->  " ++ (show pr_pre))
  --traceIO ("Pr_post: " ++ (show posts) ++ "  -->  " ++ (show pr_post))

  let step = performPolicyAnalysisStep args dataPath separator initialQuery colNames typeMap taskMap tableExprData attMap epsilon colTableCounts

  let beta = case fixedBeta of {Nothing -> B.defaultBeta; Just beta -> beta}
  (qr,initialError) <- step (Just beta)
  
  finalError <- repeatUntilGetBestError step initialError 0.0 beta
  let expectedCost = delta * cost

  --putStrLn $ intercalate ("\n") [show (pr_pre * 100.0), show (pr_post * 100.0), show expectedCost, show finalError]
  putStrLn $ intercalate (if alternative args then [B.unitSeparator2] else "\n\n") [show (pr_pre * 100.0), show (pr_post * 100.0), show expectedCost, show finalError]
  -- for PRISMS graphs, we have modified the output, adjusting it to histograms
  -- putStrLn $ intercalate (if alternative args then ";" else "\n\n") [show delta, show qr, show finalError]


repeatUntilGetBestError :: (Maybe Double -> IO (Double,Double)) -> Double -> Double -> Double -> IO Double
repeatUntilGetBestError step prevError betaMin betaMax = do
    let beta = (betaMax + betaMin) / 2.0
    (_,nextError) <- step (Just beta)
    --putStrLn $ show (beta, nextError)
    let curError = min prevError nextError
    if (betaMax - betaMin > 0.001) && (betaMax > 0.001)
      then do
        --do binary search
        if (prevError >= nextError) then do
            repeatUntilGetBestError step curError betaMin beta
        else do
            repeatUntilGetBestError step curError beta betaMax
      else do
        -- if the error tends to decrease with beta, set beta=0.0
        if (prevError > nextError) then do
            (_,finalError) <- step (Just 0.0)
            return finalError
        else do
            return nextError

performPolicyAnalysisStep :: ProgramOptions -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [(String, B.TableExpr, (String,String,String))] -> M.Map String VarState -> Double -> [Int] -> Maybe Double -> IO (Double,Double)
performPolicyAnalysisStep args dataPath separator initialQuery colNames typeMap taskMap tableExprData attMap epsilon colTableCounts beta = do

  (qr,taskAggr) <- BQ.performAnalyses args epsilon beta dataPath separator initialQuery colNames typeMap taskMap [] tableExprData attMap [] colTableCounts
  let resultMap = M.fromList $ snd (last taskAggr)

  -- take the main results, which is "for all tables"
  let (b, sds) = resultMap ! B.resultForAllTables

  -- if we choose beta that is not compatible with epsilon during optimization, we get a negative b, so the combination is considered as bad
  let relativeError = if b > 0 then (sds / b) / qr * 100 else 1/0

  -- for PRISMS graphs, we temporarily use absolute errors instead of relative errors here
  -- let relativeError = if b > 0 then sds / b else 1/0
  return (qr, relativeError)

