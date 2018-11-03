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


performDPAnalysis :: ProgramOptions -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [String] -> [(String, B.TableExpr, (String,String,String))] -> M.Map String VarState -> [(String, Maybe Double)] -> IO ()
performDPAnalysis args dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs = do

  let epsilon = getEpsilon args
  let beta    = getBeta args
  --(qr,taskAggr) <- BQ.performAnalyses args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap [("t11",Just 7),("t12",Just (1/0))]
  (qr,taskAggr) <- BQ.performAnalyses args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs
  let taskStr = if alternative args then
          map (\(taskName,res) -> taskName ++ [B.unitSeparator] ++
                  (intercalate [B.unitSeparator] $ concat $ map (\ (tableName, (b,sds)) -> [tableName, show sds, show qr, show (sds/b), show ((sds/b) / qr * 100)]) res)) taskAggr
      else
          map (\(taskName,res) -> taskName ++ "\n" ++
                  (intercalate "\n" $ map (\ (tableName, (b,sds)) -> printf "%s: %0.6f\t %0.6f\t %0.6f\t %0.3f" tableName sds qr (sds/b) ((sds/b) / qr * 100)) res)) taskAggr
  putStrLn $ intercalate (if alternative args then [B.unitSeparator2] else "\n\n") taskStr


performPolicyAnalysis :: ProgramOptions -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [(String, B.TableExpr, (String,String,String))] -> [(M.Map String VarState, Double)] -> M.Map String VarState -> IO ()
performPolicyAnalysis args dataPath separator initialQuery colNames typeMap taskMap tableExprData plcMaps attMap = do

  -- the input epsilon now works as delta, the upper bound on attacker's advantage
  let debug = not (alternative args)
  let delta = getEpsilon args
  let fixedBeta = getBeta args

  -- process the policy and the attacker knowledge
  let plainTypeMaps = map (\(tname,tmap) -> map (\(x,y) -> (tname ++ "." ++ x,y)) tmap) typeMap
  let plainTypeMap  = M.fromList $ concat plainTypeMaps

  -- TODO probabily we find a way to analyse several different policies at once here?
  -- check the variables are agregated correctly 
  let cost = sum $ map snd plcMaps

  let bss  = map (extract_bs attMap . fst) plcMaps
  let rss   = zipWith filterWith bss $ map (extract_rs attMap . fst) plcMaps
  let rrss' = zipWith filterWith bss $ map (extract_Rs attMap plainTypeMap . fst) plcMaps
  let crss' = zipWith filterWith bss $ map (extract_CRs attMap plainTypeMap . fst) plcMaps

  let rrss = zipWith (zipWith (/)) rrss' rss --rescaled bounds
  let crss = zipWith (zipWith (/)) crss' rss --rescaled bounds

  -- the weights of separate blocks in the sensitive area
  let pss  = map (map (\cr -> if cr == 0 then 1.0 else 1 / cr)) crss

  -- space dimensionality comes from the total number of sensitive variables
  -- TODO check if there are any repeating variables!
  let allSensVars = S.fromList $ concat (map (M.keys . fst) plcMaps) 
  let m = fromIntegral $ length (concat rss)

  -- we multiply the dimensions of variables belonging to one sensitive set
  -- we add the weights of different sensitive sets, since the attacker may guess any of them
  -- TODO do not include repeating vaariables into the intersection weight
  let intersectionWeight = product $ map product pss
  let total = 1 / intersectionWeight -- basically meant for discrete values, how much choices the are in total if we take X' as a unit
  let p = (sum $ map product pss) - (fromIntegral (length pss - 1)) * intersectionWeight
  let xWeight = p * total

  -- TODO continue from here
  let rrs = head rrss

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

  traceIO (show plcMaps)
  traceIO (show allSensVars)
  traceIO ("m: " ++ (show m))
  traceIO ("pss: " ++ (show pss))
  traceIO ("p: " ++ (show p))
  traceIO ("total: " ++ (show total))
  traceIO ("d: " ++ (show d))
  traceIO ("a': " ++ (show a'))
  traceIO ("rrs: " ++ (show rrs))
  traceIO ("crss: " ++ (show crss))
  traceIO ("eps': " ++ (show epsilon'))

  -- in the case a > rr for some rr, set a = rr
  let ass = map (map (\rr -> min rr a')) rrss
  let a = foldr max 0 (concat ass)

  -- TODO use some better detection of discrete choice than a = 1.0 here
  let xbarWeight = if a == 1.0 then total - xWeight else (sum $ map product ass) - xWeight

  -- recompute a and the epsilon
  let epsilon = log ((xbarWeight / xWeight) / (ub**(-1) - 1)) / a
  traceIO ("a: " ++ (show a))
  traceIO ("x: " ++ (show xWeight))
  traceIO ("xbar: " ++ (show xbarWeight))
  traceIO ("eps: " ++ (show epsilon))

  let pr_pre  = p
  let pr_post = 1 / (1 + exp(- a * epsilon) * (xbarWeight / xWeight))

  --traceIO ("Pr_pre: " ++ (show ps) ++ "  -->  " ++ (show pr_pre))
  --traceIO ("Pr_post: " ++ (show posts) ++ "  -->  " ++ (show pr_post))

  let step = performPolicyAnalysisStep args dataPath separator initialQuery colNames typeMap taskMap tableExprData attMap epsilon

  let beta = case fixedBeta of {Nothing -> B.defaultBeta; Just beta -> beta}
  (qr,initialError) <- step (Just beta)
  
  finalError <- repeatUntilGetBestError step initialError 0.0 beta
  let expectedCost = delta * cost

  putStrLn $ intercalate ("\n") [show (pr_pre * 100.0), show (pr_post * 100.0), show expectedCost, show finalError]
  putStrLn $ intercalate (if alternative args then [B.unitSeparator2] else "\n\n") [show (pr_pre * 100.0), show (pr_post * 100.0), show expectedCost, show finalError]
  -- for PRISMS we have modified the output, adjusting it to histograms
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

performPolicyAnalysisStep :: ProgramOptions -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [(String, B.TableExpr, (String,String,String))] -> M.Map String VarState -> Double -> Maybe Double -> IO (Double,Double)
performPolicyAnalysisStep args dataPath separator initialQuery colNames typeMap taskMap tableExprData attMap epsilon beta = do

  (qr,taskAggr) <- BQ.performAnalyses args epsilon beta dataPath separator initialQuery colNames typeMap taskMap [] tableExprData attMap []
  --traceIO "######################################"
  --traceIO (show taskAggr)
  let resultMap = M.fromList $ snd (last taskAggr)
  -- since we aggregate in a different way, take all results except the one "for all tables"
  -- each pair quantifies the noise that protects some variable in the policy
  -- since the attacker wins if he guesses all of them, it suffices to hide at least one, which is the minimal noise
  let b_sds_pairs = M.elems (M.filterWithKey (\k v -> k /= B.resultForAllTables) resultMap)

  let relativeErrors = map (\(b,sds) -> (sds/b) / qr * 100) b_sds_pairs
  -- for PRISMS we temporarily use absolute errors instead of relative errors here
  -- let relativeErrors = map (\(b,sds) -> sds / b) b_sds_pairs

  return (qr, foldr max 0 relativeErrors)

  -- TODO this is used in the case where the bounds are computed in a different way
  -- discard errors 0 since it means that these tables do not contain the sensitive variables
  -- however, if all the errors are 0, then the result is indeed 0
  --let relativeNonzeroErrors = filter (> 0) relativeErrors
  --return (qr, if length relativeNonzeroErrors == 0 then 0 else foldr min (1/0) relativeNonzeroErrors)


