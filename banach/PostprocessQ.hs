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

performDPAnalysis :: ProgramOptions -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [String] -> [(String, B.TableExpr, (String,String,String))] -> M.Map String VarState -> IO ()
performDPAnalysis args dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap = do

  let epsilon = getEpsilon args
  let beta    = getBeta args
  (qr,taskAggr) <- BQ.performAnalyses args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap
  let taskStr = if alternative args then
          map (\(taskName,res) -> taskName ++ [B.unitSeparator] ++
                  (intercalate [B.unitSeparator] $ concat $ map (\ (tableName, (b,sds)) -> [tableName, show sds, show qr, show (sds/b), show ((sds/b) / qr * 100)]) res)) taskAggr
      else
          map (\(taskName,res) -> taskName ++ "\n" ++
                  (intercalate "\n" $ map (\ (tableName, (b,sds)) -> printf "%s: %0.6f\t %0.6f\t %0.6f\t %0.3f" tableName sds qr (sds/b) ((sds/b) / qr * 100)) res)) taskAggr
  putStrLn $ intercalate (if alternative args then [B.unitSeparator2] else "\n\n") taskStr


performPolicyAnalysis :: ProgramOptions -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [(String, B.TableExpr, (String,String,String))] -> M.Map String (M.Map String VarState, Double) -> M.Map String VarState -> IO ()
performPolicyAnalysis args dataPath separator initialQuery colNames typeMap taskMap tableExprData plcMapMap attMap = do

  -- TODO make a bit more honest solution and check if a_i < R_i

  -- the input epsilon now works as delta, the upper bound on attacker's advantage
  let debug = not (alternative args)
  let delta = getEpsilon args
  let fixedBeta = getBeta args

  -- process the policy and the attacker knowledge
  let tableNames = M.keys plcMapMap
  let plainTypeMaps = map (\(tname,tmap) -> map (\(x,y) -> (tname ++ "." ++ x,y)) tmap) typeMap
  let plainTypeMap  = M.fromList $ concat plainTypeMaps
  let ms = map (\tableName -> let (plcMap,_) = plcMapMap ! tableName in extract_ms tableName attMap plcMap) tableNames
  let rss = map (\tableName -> let (plcMap,_) = plcMapMap ! tableName in extract_rs tableName attMap plcMap) tableNames
  let rrss = map (\tableName -> let (plcMap,_) = plcMapMap ! tableName in extract_Rs tableName attMap plcMap plainTypeMap) tableNames
  let cs = map (\tableName -> let (_,c) = plcMapMap ! tableName in c) tableNames
  let pss = zipWith (\rs rrs -> zipWith (\r rr -> if rr == 0 then 1.0 else r / rr) rs rrs) rss rrss

  --traceIO ("rss: " ++ (show rss))
  --traceIO ("Rss: " ++ (show rrss))
  --traceIO ("pss: " ++ (show pss))
  --traceIO ("cs: " ++ (show cs))
  --traceIO ("ms: " ++ (show ms))

  -- convert guessing probability to epsilon
  let e = exp 1
  let pr_pre = map product pss
  let es = zipWith (\p m -> (p + delta)**(1 / (fromIntegral m)) / e) pr_pre ms
  let epsilon = foldr min (1/0) es

  --traceIO ("es: " ++ (show es))
  --traceIO ("epsilon: " ++ (show epsilon))
  let pr_post = map (\m -> if m == 0 then 1.0 else (epsilon * e) ** (fromIntegral m)) ms

  --traceIO ("Pr_pre: " ++ (show pr_pre))
  --traceIO ("Pr_post: " ++ (show pr_post))

  let step = performPolicyAnalysisStep args dataPath separator initialQuery colNames typeMap taskMap tableExprData attMap epsilon

  let beta = case fixedBeta of {Nothing -> B.defaultBeta; Just beta -> beta}
  initialError <- step (Just beta)
  
  finalError <- repeatUntilGetBestError step initialError 0.0 beta
  let expectedCost = delta * (sum cs)

  putStrLn $ intercalate (if alternative args then [B.unitSeparator2] else "\n\n") [show ((product pr_pre)  * 100.0), show ((product pr_post)  * 100.0), show expectedCost, show finalError]

repeatUntilGetBestError :: (Maybe Double -> IO Double) -> Double -> Double -> Double -> IO Double
repeatUntilGetBestError step prevError betaMin betaMax = do
    let beta = (betaMax + betaMin) / 2.0
    nextError <- step (Just beta)
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
            finalError <- step (Just 0.0)
            return finalError
        else do
            return nextError

performPolicyAnalysisStep :: ProgramOptions -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [(String, B.TableExpr, (String,String,String))] -> M.Map String VarState -> Double -> Maybe Double -> IO Double
performPolicyAnalysisStep args dataPath separator initialQuery colNames typeMap taskMap tableExprData attMap epsilon beta = do

  (qr,taskAggr) <- BQ.performAnalyses args epsilon beta dataPath separator initialQuery colNames typeMap taskMap [] tableExprData attMap
  let resultMap = M.fromList $ snd (last taskAggr)
  let (b,sds) = resultMap ! B.resultForAllTables
  let relativeError = ((sds/b) / qr * 100)
  return relativeError


