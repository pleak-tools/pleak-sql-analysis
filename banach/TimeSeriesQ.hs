module TimeSeriesQ where

import Control.Monad
import Data.List
import Text.Printf
import qualified Data.Map as Map

import ProgramOptions
import PolicyQ
import Banach(gamma)
import BanachQ(AnalysisDataWrtTable(..), DataWrtTable(..), TaskMap, performAnalyses)

addWhereCond :: String -> DataWrtTable -> DataWrtTable
addWhereCond cond (DWT (ADWT x1 x2 x3 (x4sensCond,x4from,x4where)) x5 x6 x7 x8) = DWT (ADWT x1 x2 x3 (x4sensCond,x4from, if x4where == "" then cond else cond ++ " AND (" ++ x4where ++ ")")) x5 x6 x7 x8

performTimeSeriesDPAnalysis :: String -> ProgramOptions -> String -> String -> String -> String -> [String] -> Int -> [String] -> [(String,[(String, String)])] -> TaskMap -> [String] -> [DataWrtTable] -> AttMap -> [(String, Maybe Double)] -> [Int] -> IO ()
performTimeSeriesDPAnalysis timeCol args outputTableName dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

  let debug    = not (alternative args)
  let epsilon  = getEpsilon args
  let beta     = getBeta args
  let delta    = getDelta args

  when debug $ printf "epsilon = %0.6f\n" epsilon
  when debug $ printf "gamma = %0.6f\n" gamma

  contents <- getContents
  foldM_ (\ (time0,state,releases) line0 -> do
    let time = time0 + 1
    printf "time point #%d\n" time
    let (debug,silent,line) = case line0 of 'D' : line -> (True,False,line)
                                            'd' : line -> (True,True, line)
                                            line       -> (False,True,line)
    --when debug $ putStrLn "tableExprData:"
    --when debug $ print tableExprData
    let tableExprData2 = map (addWhereCond (timeCol ++ " = " ++ line)) tableExprData
    when debug $ putStrLn "tableExprData2:"
    when debug $ print tableExprData2

    (qmap, taskAggr, queryResult) <- performAnalyses args silent epsilon beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData2 attMap tableGs colTableCounts

    when debug $ putStrLn "qmap:"
    when debug $ print qmap
    when debug $ putStrLn "taskAggr:"
    when debug $ print taskAggr
    printf "change in query result = %0.6f\n" queryResult
    let (b,sensitivity) = snd $ head $ filter ((== "all input tables together") . fst) $ snd $ head $ taskAggr Map.! []
    when debug $ printf "sensitivity = %0.6f\n" sensitivity
    when debug $ printf "b = %0.6f\n" b
    let beta = epsilon / (gamma + 1) - b
    when debug $ printf "beta = %0.6f\n" beta
    let noiseLevel = sensitivity / b
    printf "noise level = %0.6f\n" noiseLevel
    let state' = map (\ (value, noiseLev) -> (value + queryResult, max noiseLev noiseLevel)) state
    when debug $ printf "state' = %s\n" (show state')
    let
      addRelease :: (Int,Int,Double,Double) -> [(Int,Int,Double,Double)] -> [(Int,Int,Double,Double)]
      addRelease r [] = [r]
      addRelease r@(t1,t2,val,nl) rs@((t1',t2',val',nl'):rs') | t1 <= t1' = addRelease r rs'
                                                              | otherwise = r : rs

      processReleases :: Int -> Int -> [(Double,Double)] -> [(Int,Int,Double,Double)] -> IO ([(Double,Double)], [(Int,Int,Double,Double)])
      processReleases len n (s1:s) rs = do
        let (val,nl) = s1
        if odd n
          then do printf "Release x[%d-%d] = %0.6f ± %0.6f\n" (time - len + 1) time val nl
                  return ((0,0) : (case s of [] -> [s1]; _  -> s), addRelease ((time - len + 1),time,val,nl) rs)
          else do (s',rs') <- processReleases (len * 2) (n `div` 2) s rs
                  return ((0,0):s', rs')

    (state'',releases') <- processReleases 1 time state' releases
    when debug $ printf "state'' = %s\n" (show state'')
    when debug $ printf "releases' = %s\n" (show releases')
    let totalUsedEpsilon = epsilon * fromIntegral (length state'' - 1)
    printf "total epsilon used so far = %0.6f\n" totalUsedEpsilon

    printf "Query result at time point #%d = r[%d]\n" time time
    printf "r[%d] = %s\n" time (intercalate " + " $ map (\ (t1,t2,val,nl) -> printf "x[%d-%d]" t1 t2) releases')
    forM_ releases' $ \ (t1,t2,val,nl) -> printf "x[%d-%d] = %0.6f ± %0.6f\n" t1 t2 val nl
    let (_,_,vals,nls) = unzip4 releases'
    let val = sum vals
    let nl = sqrt (sum (map (^2) nls))
    printf "r[%d] = %0.6f ± %0.6f\n" time val nl

    return (time,state'',releases')) (0::Int,[(0,0)],[]) (lines contents)

  return ()
