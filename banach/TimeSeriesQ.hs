module TimeSeriesQ where

import Control.Monad
import Data.List
import Data.List.Split
import Text.Printf
import qualified Data.Map as Map

import ProgramOptions
import DatabaseQ
import PolicyQ
import Banach(gamma)
import BanachQ(AnalysisDataWrtTable(..), DataWrtTable(..), TaskMap, performAnalyses)

budgetSuffix :: String
budgetSuffix = "_budget"

addWhereCond :: String -> DataWrtTable -> DataWrtTable
addWhereCond cond (DWT (ADWT x1 x2 x3 (x4sensCond,x4from,x4where)) x5 x6 x7 x8) = DWT (ADWT x1 x2 x3 (x4sensCond,x4from, if x4where == "" then cond else cond ++ " AND (" ++ x4where ++ ")")) x5 x6 x7 x8

getFromAndWhere :: DataWrtTable -> String
getFromAndWhere (DWT (ADWT x1 x2 x3 (x4sensCond,x4from,x4where)) x5 x6 x7 x8) = (if x4from == "" then "" else " FROM " ++ x4from) ++ (if x4where == "" then "" else " WHERE " ++ x4where)

groupByFst :: (Ord a) => [(a,b)] -> [(a,[b])]
groupByFst = map (\ g -> (fst (head g), map snd g)) . groupBy (\ x y -> fst x == fst y) . sortBy (\ x y -> compare (fst x) (fst y))

performTimeSeriesDPAnalysis :: String -> [String] -> [String] -> ProgramOptions -> String -> String -> String -> String -> [String] -> Int -> [String] -> [(String,[(String, String)])] -> TaskMap -> [String] -> [DataWrtTable] -> AttMap ->
                               [(String, Maybe Double)] -> [Int] -> IO ()
performTimeSeriesDPAnalysis timeCol tableNames tableAliases args outputTableName dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

  let debug    = not (alternative args)
  let epsilon  = getEpsilon args
  let beta     = getBeta args
  let delta    = getDelta args

  when debug $ printf "epsilon = %0.6f\n" epsilon
  when debug $ printf "gamma = %0.6f\n" gamma
  --when debug $ printf "typeMap = %s\n" (show typeMap)
  --when debug $ printf "taskMap = %s\n" (show taskMap)
  --when debug $ printf "attMap = %s\n" (show attMap)
  --when debug $ printf "tableGs = %s\n" (show tableGs)
  --when debug $ printf "colTableCounts = %s\n" (show colTableCounts)
  when debug $ printf "tableNames = %s\n" (show tableNames)
  when debug $ printf "tableAliases = %s\n" (show tableAliases)

  let tablesAndAliases = groupByFst $ zip tableNames tableAliases
  let tableToAliasesMap = Map.fromList tablesAndAliases
  let uniqueTables = map fst tablesAndAliases
  createBudgetTablesQueries <- fmap concat $ forM uniqueTables $ \ t -> do
    let budgetTable = t ++ budgetSuffix
    let query1 = "DROP TABLE IF EXISTS " ++ budgetTable
    let query2 = "CREATE TABLE " ++ budgetTable ++ " (ID int8, budget double precision)"
    when debug $ putStrLn query1
    when debug $ putStrLn query2
    return [query1, query2]
  sendQueriesToDbAndCommit args createBudgetTablesQueries

  let getMaxBudgetQuery = "SELECT max(m) FROM (" ++ (intercalate " UNION " $ map (\ t -> "(SELECT max(budget) as m FROM " ++ t ++ budgetSuffix ++ ")") uniqueTables) ++ ") as sub"
  when debug $ putStrLn getMaxBudgetQuery

  contents <- getContents
  foldM_ (\ (time0,state,releases) line0 -> do
    let time = time0 + 1
    printf "time point #%d\n" time
    let (debug,silent,line) = case line0 of 'D' : line -> (True,False,line)
                                            'd' : line -> (True,True, line)
                                            line       -> (False,True,line)
    let
      releaseInterval :: Int -> Int -> IO (Double,Double)
      releaseInterval time1 time2 = do
        printf "Releasing time interval %d-%d\n" time1 time2
        let timeCols = splitOn "," timeCol
        let
          timeCols2 =
            concatMap (\ tc -> let [table,col] = splitOn "." tc in
                               let tas = tableToAliasesMap Map.! table in
                               map (\ ta -> ta ++ "." ++ col) tas)
                timeCols
        let maxTimeStr = case timeCols2 of [c] -> c
                                           cs  -> "GREATEST(" ++ intercalate "," cs ++ ")"
        when debug $ printf "maxTimeStr = %s\n" maxTimeStr
        let tableExprData2 = map (addWhereCond (maxTimeStr ++ " BETWEEN " ++ show time1 ++ " AND " ++ show time2)) tableExprData
        when debug $ putStrLn "tableExprData2:"
        when debug $ print tableExprData2

        when debug $ putStrLn "Computing rows used by the query:"
        createBudgetsQueries <- fmap concat $ forM tablesAndAliases $ \ (tn, tas) -> do
          when debug $ printf "Table %s AS %s:\n" tn (show tas)
          let usedRowsQueries = map (\ ta -> "SELECT DISTINCT " ++ ta ++ ".ID" ++ getFromAndWhere (head tableExprData2)) tas
          let usedRowsQuery = case usedRowsQueries of [q] -> q
                                                      qs  -> intercalate " UNION " $ map (\ q -> '(' : q ++ ")") qs
          when debug $ putStrLn usedRowsQuery
          let budgetTable = tn ++ budgetSuffix
          let rowsHavingBudgetQuery = "SELECT DISTINCT id FROM " ++ budgetTable
          let usedRowsWithoutBudgetQuery = "(" ++ usedRowsQuery ++ ") EXCEPT (" ++ rowsHavingBudgetQuery ++ ")"
          let createBudgetsQuery = "INSERT INTO " ++ budgetTable ++ " (id,budget) SELECT *, 0 as budget FROM (" ++ usedRowsWithoutBudgetQuery ++ ") as sub"
          let updateBudgetsQuery = "UPDATE " ++ budgetTable ++ " SET budget = budget + " ++ show epsilon ++ " WHERE id IN (" ++ usedRowsQuery ++ ")"
          when debug $ putStrLn createBudgetsQuery
          when debug $ putStrLn updateBudgetsQuery
          return [createBudgetsQuery, updateBudgetsQuery]

        (qmap, taskAggr, queryResult) <- performAnalyses args silent epsilon beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData2 attMap tableGs colTableCounts
        sendQueriesToDbAndCommit args createBudgetsQueries

        printf "change in query result = %0.6f\n" queryResult
        let (b,sensitivity) = snd $ head $ filter ((== "all input tables together") . fst) $ snd $ head $ taskAggr Map.! []
        when debug $ printf "sensitivity = %0.6f\n" sensitivity
        when debug $ printf "b = %0.6f\n" b
        let beta = epsilon / (gamma + 1) - b
        when debug $ printf "beta = %0.6f\n" beta
        let noiseLevel = sensitivity / b
        printf "noise level = %0.6f\n" noiseLevel
        return (queryResult, noiseLevel)

    let state' = map (\ (value, noiseLev) -> (value + 0, max noiseLev 0)) state
    --let state' = map (\ (value, noiseLev) -> (value + queryResult, max noiseLev noiseLevel)) state
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
          then do let time1 = time - len + 1
                  let time2 = time
                  (val,nl) <- releaseInterval time1 time2
                  printf "Release x[%d-%d] = %0.6f ± %0.6f\n" time1 time2 val nl
                  return ((0,0) : (case s of [] -> [s1]; _  -> s), addRelease (time1,time2,val,nl) rs)
          else do (s',rs') <- processReleases (len * 2) (n `div` 2) s rs
                  return ((0,0):s', rs')

    (state'',releases') <- processReleases 1 time state' releases
    when debug $ printf "state'' = %s\n" (show state'')
    when debug $ printf "releases' = %s\n" (show releases')
    --let totalUsedEpsilon = epsilon * fromIntegral (length state'' - 1)
    totalUsedEpsilon <- sendDoubleQueryToDb args getMaxBudgetQuery
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
