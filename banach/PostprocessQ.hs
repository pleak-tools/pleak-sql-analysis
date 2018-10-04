module PostprocessQ where

import Debug.Trace

import Data.List
import qualified Data.Map as M
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

performDPAnalysis :: ProgramOptions -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [String] -> [(String, B.TableExpr, (String,String,String))] -> M.Map String VarState -> IO ()
performDPAnalysis args dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap = do

  let epsilon = getEpsilon args
  let beta    = getBeta args
  --(qr,taskAggr) <- BQ.performAnalyses args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap [("t11",Just 7),("t12",Just (1/0))]
  (qr,taskAggr) <- BQ.performAnalyses args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap []
  let taskStr = if alternative args then
          map (\(taskName,res) -> taskName ++ [B.unitSeparator] ++
                  (intercalate [B.unitSeparator] $ concat $ map (\ (tableName, (b,sds)) -> [tableName, show sds, show qr, show (sds/b), show ((sds/b) / qr * 100)]) res)) taskAggr
      else
          map (\(taskName,res) -> taskName ++ "\n" ++
                  (intercalate "\n" $ map (\ (tableName, (b,sds)) -> printf "%s: %0.6f\t %0.6f\t %0.6f\t %0.3f" tableName sds qr (sds/b) ((sds/b) / qr * 100)) res)) taskAggr
  putStrLn $ intercalate (if alternative args then [B.unitSeparator2] else "\n\n") taskStr


performPolicyAnalysis :: ProgramOptions -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [(String, B.TableExpr, (String,String,String))] -> Double -> M.Map String VarState -> M.Map String VarState -> IO ()
performPolicyAnalysis args dataPath separator initialQuery colNames typeMap taskMap tableExprData cost plcMap attMap = do

  -- the input epsilon now works as delta, the upper bound on attacker's advantage
  let debug = not (alternative args)
  let delta = getEpsilon args
  let fixedBeta = getBeta args

  -- process the policy and the attacker knowledge
  let plainTypeMaps = map (\(tname,tmap) -> map (\(x,y) -> (tname ++ "." ++ x,y)) tmap) typeMap
  let plainTypeMap  = M.fromList $ concat plainTypeMaps

  -- TODO probabily we find a way to analyse several different policies at once here?
  -- check the variables are agregated correctly 
  let bs  = extract_bs attMap plcMap

  let rs  = filterWith bs (extract_rs attMap plcMap)
  let rrs = filterWith bs (extract_Rs attMap plcMap plainTypeMap)
  let ps  = zipWith (\r rr -> if rr == 0 then 1.0 else r / rr) rs rrs
  let p = product ps

  --traceIO ("rs: " ++ (show rs))
  --traceIO ("Rs: " ++ (show rrs))
  --traceIO ("p: "  ++ (show p))

  -- we know that the probability cannot grow above 100%
  let d = min (1 - p) delta
  -- the upper bound for the multivariate case
  let ub = (p + d)**(1 / fromIntegral (length ps))

  -- convert guessing probability to epsilon
  let es' = map (\r -> (lambert (ub / (exp(1) * (1 - ub))) 10) / r) rs

  -- find the values of a that correspond to epsilons
  let as' = zipWith (\e r -> r + 1 / e) es' rs

  -- in the case a > R, set a = R and recompute the corresponding epsilon
  let es = zipWith3 (\e a rr -> if a > rr then (log (ub * (1 - p) / (p * (1 - ub)))) / rr else e) es' as' rrs
  let as = zipWith (\a rr -> if a > rr then rr else a) as' rrs

  --traceIO ("as': " ++ (show as'))
  --traceIO ("as: "  ++ (show as))
  --traceIO ("es': " ++ (show es'))
  --traceIO ("es: "  ++ (show es))

  -- TODO we will actually use list es to find more precise bounds, and epsilon itself is only needed since the interface requires it
  -- currently, we do it in the other way since we need to remember which epsilon corresponds to which output
  -- we take the smallest epsilon for safety
  let epsilon = foldr min (1/0) es  
  let posts = zipWith3 (\a e r -> 1 / (1 + exp(- a * e) * (a / r - 1))) as es rs

  let pr_pre  = p
  let pr_post = product $ posts

  --traceIO ("Pr_pre: " ++ (show ps) ++ "  -->  " ++ (show pr_pre))
  --traceIO ("Pr_post: " ++ (show posts) ++ "  -->  " ++ (show pr_post))

  let step = performPolicyAnalysisStep args dataPath separator initialQuery colNames typeMap taskMap tableExprData attMap epsilon

  let beta = case fixedBeta of {Nothing -> B.defaultBeta; Just beta -> beta}
  (qr,initialError) <- step (Just beta)
  
  finalError <- repeatUntilGetBestError step initialError 0.0 beta
  let expectedCost = delta * cost

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


