module TimeSeriesQ where

import Control.Monad
import Data.List
import Data.List.Split
import Text.Printf
import qualified Data.Set as Set
import qualified Data.Map as Map

import ProgramOptions
import DatabaseQ
import PolicyQ
import Banach(gamma)
import BanachQ(AnalysisDataWrtTable(..), DataWrtTable(..), TaskMap, performAnalyses, findMaximumGsens, findGub, findModifiedQuery)

budgetSuffix :: String
budgetSuffix = "_budget"

budgetAliasSuffix :: String
budgetAliasSuffix = "_budgetalias"

provenanceBudgetTable :: String
provenanceBudgetTable = "provenancebudget"

usedRowsTable :: String
usedRowsTable = "usedrowsinjoinedtable"

-- multiply the used budget by this factor to avoid the budget being exceeded by an infinitesimal amount due to floating-point rounding errors that can cause a row use to be excluded
roundDownFactor :: Double
roundDownFactor = (1 :: Double) - (2e-14 :: Double)

addWhereCond :: String -> DataWrtTable -> DataWrtTable
addWhereCond cond (DWT (ADWT x1 x2 x3 (x4sensCond,x4from,x4where)) x5 x6 x7 x8) = DWT (ADWT x1 x2 x3 (x4sensCond,x4from, if x4where == "" then cond else "(" ++ cond ++ ") AND (" ++ x4where ++ ")")) x5 x6 x7 x8

addFrom :: String -> DataWrtTable -> DataWrtTable
addFrom extraFrom (DWT (ADWT x1 x2 x3 (x4sensCond,x4from,x4where)) x5 x6 x7 x8) = DWT (ADWT x1 x2 x3 (x4sensCond, if x4from == "" then extraFrom else x4from ++ ", " ++ extraFrom, x4where)) x5 x6 x7 x8

addFroms :: [String] -> DataWrtTable -> DataWrtTable
addFroms []         = id
addFroms extraFroms = addFrom (intercalate ", " extraFroms)

getFromAndWhere :: DataWrtTable -> String
getFromAndWhere (DWT (ADWT x1 x2 x3 (x4sensCond,x4from,x4where)) x5 x6 x7 x8) = (if x4from == "" then "" else " FROM " ++ x4from) ++ (if x4where == "" then "" else " WHERE " ++ x4where)

groupByFst :: (Ord a) => [(a,b)] -> [(a,[b])]
groupByFst = map (\ g -> (fst (head g), map snd g)) . groupBy (\ x y -> fst x == fst y) . sortBy (\ x y -> compare (fst x) (fst y))

floorLog2 :: Int -> Int
floorLog2 n | n <= 0 = -1
            | otherwise = floorLog2 (n `div` 2) + 1
-- maximum number of times the budget of a provenance is used when a fixed amount of budget is used per row use
maxBudgetUses :: ProgramOptions -> Int -> Int
maxBudgetUses args n = (floorLog2 n + 1) * (case maxProvUses args of Just mpu -> mpu; Nothing -> 1)
-- maximum number of times the budget of a provenance is used when a fixed amount of budget is used per time period when a row is used
maxBudgetTimeperiods :: ProgramOptions -> Int -> Int
maxBudgetTimeperiods args n =
  -- compute the number of intervals with each power-of-two length released so far
  let f 0 = []
      f n = let m = n `div` 2 in (n - m) : f m
  in sum $ map (min (maxProvTimepoints args)) $ f n


performTimeSeriesDPAnalysis :: String -> [String] -> [String] -> ProgramOptions -> String -> String -> String -> String -> [String] -> Int -> [String] -> [(String,[(String, String)])] -> TaskMap -> [String] -> [DataWrtTable] -> AttMap ->
                               [(String, Maybe Double)] -> [Int] -> IO ()
performTimeSeriesDPAnalysis timeCol tableNames tableAliases args outputTableName dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

  let debug    = not (alternative args)
  let epsilon0 = getEpsilon args
  let beta0    = getBeta args
  let delta0   = getDelta args
  let (epsilon,beta,delta) =
        case maxTimepoints args of
          Just mTimepoints -> let mbtp = fromIntegral (maxBudgetTimeperiods args mTimepoints) / roundDownFactor
                              in (epsilon0/mbtp, fmap (/mbtp) beta0, delta0/mbtp)
          Nothing          -> (epsilon0, beta0, delta0)

  when debug $ printf "epsilon = %0.6f\n" epsilon
  when debug $ printf "beta = %s\n" (show beta)
  when debug $ printf "gamma = %0.6f\n" gamma
  --when debug $ printf "typeMap = %s\n" (show typeMap)
  --when debug $ printf "taskMap = %s\n" (show taskMap)
  --when debug $ printf "attMap = %s\n" (show attMap)
  when debug $ printf "tableGs = %s\n" (show tableGs)
  --when debug $ printf "colTableCounts = %s\n" (show colTableCounts)
  when debug $ printf "tableNames = %s\n" (show tableNames)
  when debug $ printf "tableAliases = %s\n" (show tableAliases)
  when debug $ printf "initQueries:\n%s\n" (intercalate "\n" initQueries)

  when debug $ putStrLn "================================="
  when debug $ putStrLn "Computing queries that create empty intermediate query tables and the input tables\n"
  sendQueriesToDbAndCommit args initQueries

  let tablesAndAliases = groupByFst $ zip tableNames tableAliases
  let tableToAliasesMap = Map.fromList tablesAndAliases
  let uniqueTables = map fst tablesAndAliases

  let tableGmap = Map.fromList tableGs
  let minG = minimum $ concatMap (\ t -> case Map.lookup t tableGmap of
                Nothing            -> case getG args of Just g -> [g]
                Just Nothing       -> []
                Just (Just tableG) -> [tableG]) uniqueTables
  when debug $ printf "minG = %f\n" minG

  maxGsens <- findMaximumGsens args False epsilon beta dataPath separator initialQuery colNames typeMap sensitiveVarList tableExprData attMap tableGs colTableCounts
  when debug $ printf "maxGsens = %f\n" maxGsens
  gub <- findGub args False epsilon beta dataPath separator initialQuery colNames typeMap sensitiveVarList tableExprData attMap tableGs colTableCounts
  when debug $ printf "gub = %f\n" gub
  modifiedQuery <- findModifiedQuery args False epsilon beta dataPath separator initialQuery colNames typeMap sensitiveVarList tableExprData attMap tableGs colTableCounts
  when debug $ printf "fx = %s\n" modifiedQuery
  --(epsilon_gs,beta_pru) <-
  --  case maxTimepoints args of
  --    Just mTimepoints -> do
  --      let mbu = fromIntegral (maxBudgetUses args mTimepoints)
  --      let epsilon_gs = epsilon0 / mbu
  --      when debug $ printf "epsilon_gs = %0.6f\n" epsilon_gs
  --      let beta_pru = fmap (/ mbu) beta0
  --      when debug $ printf "beta_pru = %s\n" (show beta_pru)
  --      -- used for smoothing Banach sensitivity
  --      case beta_pru of
  --        Just beta_pru -> do
  --          let minBanachSens = exp (- beta_pru * minG / fromIntegral (if excludeExhausted args then length tableAliases + 1 else 1)) * maxGsens
  --          when debug $ printf "minBanachSens = %0.6f\n" minBanachSens
  --        Nothing -> return ()
  --      return (epsilon_gs, beta_pru)
  --    _ -> return (error "epsilon_gs", error "beta_pru")

  (useFixedBudgetPerRowUse, epsilon_gs, beta_pru, noiseLevel_gs, gs_arr) <- case (maxProvUses args, maxTimepoints args) of
    (Just mProvUses, Just mTimepoints) -> do
      let mbu = fromIntegral (maxBudgetUses args mTimepoints) / roundDownFactor
      -- epsilon allocated per row use
      let epsilon_gs = epsilon0 / mbu
      when debug $ printf "epsilon_gs = %0.6f\n" epsilon_gs
      let beta_pru = fmap (/ mbu) beta0
      when debug $ printf "beta_pru = %s\n" (show beta_pru)
      -- used for smoothing Banach sensitivity
      case beta_pru of
        Just beta_pru -> do
          let minBanachSens = exp (- beta_pru * minG / fromIntegral (if excludeExhausted args && not (oneToN args) then length tableAliases + 1 else 1)) * maxGsens
          when debug $ printf "minBanachSens = %0.6f\n" minBanachSens
        Nothing -> return ()
      -- global sensitivity for adding/removing rows
      let gs_arr = fromIntegral (if excludeExhausted args then (if oneToN args && not (increasingBudgets args) then 2 else length tableAliases + 1) else 1) * gub / minG
      when debug $ printf "gs_arr = %f\n" gs_arr
      let sensitivity_gs = max gs_arr maxGsens
      when debug $ printf "sensitivity_gs = %0.6f\n" sensitivity_gs
      let noiseLevel_gs = sensitivity_gs / epsilon_gs
      when debug $ printf "noiseLevel_gs = %0.6f\n" noiseLevel_gs
      return (True, epsilon_gs, beta_pru, noiseLevel_gs, gs_arr)
    _ -> return (False, undefined, undefined, undefined, undefined)

  let timeCols = splitOn "," timeCol
  let
    addTimeCols =
      concatMap (\ tc -> let [table,col] = splitOn "." tc in
                         case splitOn ":" col of
                           addCol : _ | not (null addCol) ->
                               let tas = tableToAliasesMap Map.! table in
                               map (\ ta -> ta ++ "." ++ addCol) tas
                           _ -> [])
          timeCols
    removeTimeCols =
      concatMap (\ tc -> let [table,col] = splitOn "." tc in
                         case splitOn ":" col of
                           addCol : removeCol : _ | not (null removeCol) ->
                               let tas = tableToAliasesMap Map.! table in
                               if null addCol
                                 then error ("Cannot have a remove time column without an add time column in table " ++ table)
                                 else map (\ ta -> ta ++ "." ++ removeCol) tas
                           _ -> [])
          timeCols
    maybeRemoveTimeCols =
      concatMap (\ tc -> let [table,col] = splitOn "." tc in
                         case splitOn ":" col of
                           addCol : removeCol : _ | not (null addCol) ->
                               let tas = tableToAliasesMap Map.! table in
                               if null removeCol
                                 then map (const Nothing) tas
                                 else map (\ ta -> Just (ta ++ "." ++ removeCol)) tas
                           _ -> [])
          timeCols
    provenanceTablesAndCols =
      concatMap (\ tc -> let [table,col] = splitOn "." tc in
                         case splitOn ":" col of
                           _ : _ : provCol : _ | not (null provCol) -> [(table, provCol)]
                           _ -> [])
          timeCols
    provenanceCols = concatMap (\ (table,col) -> let tas = tableToAliasesMap Map.! table in map (\ ta -> ta ++ "." ++ col) tas) provenanceTablesAndCols
    provenanceTablesSet = Set.fromList (map fst provenanceTablesAndCols)
    tableToProvenanceColMap = Map.fromList provenanceTablesAndCols
  let addTimeStr = case addTimeCols of [c] -> c
                                       cs  -> "GREATEST(" ++ intercalate "," cs ++ ")"
  when debug $ printf "addTimeStr = %s\n" addTimeStr
  let removeTimeStr = case removeTimeCols of []  -> ""
                                             [c] -> c
                                             cs  -> "LEAST(" ++ intercalate "," cs ++ ")"
  let removesUsed = not (null removeTimeCols)
  let addsUsed = not (null addTimeCols)
  unless addsUsed $ fail "At least one add time column must be given for time series analysis"
  let provenancesUsed = not (null provenanceTablesAndCols)

  let rowUseRatios = map (\ ta -> ta ++ budgetAliasSuffix ++ ".useratio") tableAliases
  let rowUseRatio = case rowUseRatios of [c] -> c
                                         cs -> "LEAST(" ++ intercalate "," cs ++ ")"
  when debug $ when (excludeExhausted args) $ printf "rowUseRatio: %s\n" rowUseRatio
  let modifiedQueryWithExcludedRows = "SELECT sum(" ++ (if excludeExhausted args && not (oneToN args) then "(" ++ modifiedQuery ++ ") * " ++ rowUseRatio else modifiedQuery) ++ ")"
  when debug $ printf "modifiedQueryWithExcludedRows: %s\n" modifiedQueryWithExcludedRows
  let extraFromsForExcludingRows = if excludeExhausted args then if oneToN args then [usedRowsTable]
                                                                                else zipWith (\ tn ta -> (if tn `Set.member` provenanceTablesSet then provenanceBudgetTable else tn ++ budgetSuffix) ++ " AS " ++ ta ++ budgetAliasSuffix)
                                                                                             tableNames tableAliases
                                                            else []
  when debug $ printf "extraFromsForExcludingRows: %s\n" (show extraFromsForExcludingRows)
  let extraWheresForExcludingRows = if excludeExhausted args then if oneToN args then intercalate " AND " (map (\ ta -> ta ++ ".ID = " ++ usedRowsTable ++ "." ++ ta ++ "_id") tableAliases)
                                                                                 else intercalate " AND " (zipWith (\ tn ta -> ta ++ "." ++ (case Map.lookup tn tableToProvenanceColMap of
                                                                                                                                               Just provCol -> provCol
                                                                                                                                               Nothing -> "ID") ++ " = " ++ ta ++ budgetAliasSuffix ++ ".ID")
                                                                                                                   tableNames tableAliases)
                                                             else ""
  when debug $ printf "extraWheresForExcludingRows: %s\n" extraWheresForExcludingRows
  let addFromsAndWheresForExcludingRows = if excludeExhausted args then addFroms extraFromsForExcludingRows . addWhereCond extraWheresForExcludingRows else id
  let createQueryForExcludingRows tableExprData = modifiedQueryWithExcludedRows ++ getFromAndWhere (addFromsAndWheresForExcludingRows tableExprData)
  let createQueryWithoutExcludingRows tableExprData = modifiedQueryWithExcludedRows ++ getFromAndWhere tableExprData


  let
    createBudgetTableQueries :: String -> IO [String]
    createBudgetTableQueries budgetTable = do
      let query1 = "DROP TABLE IF EXISTS " ++ budgetTable
      let query2 = "CREATE TABLE " ++ budgetTable ++ (if excludeExhausted args && not (oneToN args) then " (ID int8, budget double precision, useratio double precision)" else " (ID int8, budget double precision)")
      when debug $ putStrLn query1
      when debug $ putStrLn query2
      return [query1, query2]
    makeCreateUsedRowsTableQuery :: IO [String]
    makeCreateUsedRowsTableQuery =
      if oneToN args
        then do
          let query1 = "DROP TABLE IF EXISTS " ++ usedRowsTable
          let query2 = "CREATE TABLE " ++ usedRowsTable ++ " (" ++ intercalate ", " (map (\ (tn, [ta]) -> ta ++ "_id int8") tablesAndAliases) ++ ")"
          when debug $ putStrLn query1
          when debug $ putStrLn query2
          return [query1,query2]
        else return []
  let budgetTables = map (++ budgetSuffix) (filter (`Set.notMember` provenanceTablesSet) uniqueTables) ++ (if provenancesUsed then [provenanceBudgetTable] else [])
  createBudgetTablesQueries <- fmap concat $ mapM createBudgetTableQueries budgetTables
  createUsedRowsTableQuery <- makeCreateUsedRowsTableQuery
  sendQueriesToDbAndCommit args (createBudgetTablesQueries ++ createUsedRowsTableQuery ++ createUsedRowsTableQuery)

  let getMaxBudgetQuery = "SELECT max(m) FROM (" ++ (intercalate " UNION " $ map (\ t -> "(SELECT max(budget) as m FROM " ++ t ++ ")") budgetTables) ++ ") as sub"
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
        let addCond1n = addTimeStr ++ " BETWEEN " ++ show time1 ++ " AND " ++ show time2
        let addCond1c = intercalate " AND " (("(" ++ intercalate " OR " (map (\ atc -> atc ++ ">=" ++ show time1) addTimeCols) ++ ")") : map (\ atc -> atc ++ "<=" ++ show time2) addTimeCols)
        let addCond1 = if combinedSens args then addCond1c else addCond1n
        let addCond2n = removeTimeStr ++ " > " ++ show time2
        let addCond2c = intercalate " AND " (map (\ rtc -> rtc ++ ">" ++ show time2) removeTimeCols)
        let addCond2 = if combinedSens args then addCond2c else addCond2n
        let addCond12 = "(" ++ addCond1 ++ ") AND (" ++ addCond2 ++ ")"
        let addCond = if removesUsed then addCond12 else addCond1
        let tableExprData_adds = map (addWhereCond addCond) tableExprData
        let removeCond1n = removeTimeStr ++ " BETWEEN " ++ show time1 ++ " AND " ++ show time2
        let removeCond1c = intercalate " AND " (("(" ++ intercalate " OR " (map (\ rtc -> rtc ++ "<=" ++ show time2) removeTimeCols) ++ ")") : map (\ rtc -> rtc ++ ">=" ++ show time1) removeTimeCols)
        let removeCond1 = if combinedSens args then removeCond1c else removeCond1n
        let removeCond2n = addTimeStr ++ " < " ++ show time1
        let removeCond2c = intercalate " AND " (map (\ atc -> atc ++ "<" ++ show time1) addTimeCols)
        let removeCond2 = if combinedSens args then removeCond2c else removeCond2n
        let removeCond12 = "(" ++ removeCond1 ++ ") AND (" ++ removeCond2 ++ ")"
        let removeCond = if removesUsed then removeCond12 else "false"
        let tableExprData_removes = map (addWhereCond removeCond) tableExprData
        let addOrRemoveCond1 = intercalate " AND " $ zipWith (\ atc mrtc -> case mrtc of Just rtc -> atc ++ "<=" ++ show time2 ++ " AND " ++ rtc ++ ">=" ++ show time1 ++
                                                                                                            " AND (" ++ atc ++ "<" ++ show time1 ++ " OR " ++ rtc ++ ">" ++ show time2 ++ ")"
                                                                                         Nothing  -> atc ++ "<=" ++ show time2)
                                                             addTimeCols maybeRemoveTimeCols
        let addOrRemoveCond = if combinedSens args then "(" ++ addOrRemoveCond1 ++ ") AND ((" ++ addCond12 ++ ") OR (" ++ removeCond12 ++ "))"
                                                   else "(" ++ addCond12 ++ ") OR (" ++ removeCond12 ++ ")"
        let tableExprData_addsOrRemoves = map (addWhereCond (if removesUsed then addOrRemoveCond else addCond1)) tableExprData
        when debug $ putStrLn "tableExprData_adds:"
        when debug $ print tableExprData_adds
        when debug $ putStrLn "tableExprData_removes:"
        when debug $ print tableExprData_removes
        when debug $ putStrLn "tableExprData_addsOrRemoves:"
        when debug $ print tableExprData_addsOrRemoves

        when debug $ putStrLn "Computing rows used by the query:"
        let
          createBudgetQueries :: [String] -> String -> IO [String]
          createBudgetQueries provCols budgetTable = do
            let usedRowsQueries = map (\ col -> "SELECT DISTINCT " ++ col ++ " AS id" ++ getFromAndWhere (head tableExprData_addsOrRemoves)) provCols
            let usedRowsQuery = case usedRowsQueries of [q] -> q
                                                        qs  -> intercalate " UNION " $ map (\ q -> '(' : q ++ ")") qs
            when debug $ putStrLn usedRowsQuery
            let rowsHavingBudgetQuery = "SELECT DISTINCT id FROM " ++ budgetTable
            let usedRowsWithoutBudgetQuery = "(" ++ usedRowsQuery ++ ") EXCEPT (" ++ rowsHavingBudgetQuery ++ ")"
            let createBudgetsQuery = "INSERT INTO " ++ budgetTable ++ " (id,budget) SELECT *, 0 as budget FROM (" ++ usedRowsWithoutBudgetQuery ++ ") as sub"
            let updateBudgetsQuery = "UPDATE " ++ budgetTable ++ " SET budget = budget + " ++ show epsilon ++ " WHERE id IN (" ++ usedRowsQuery ++ ")"
            when debug $ putStrLn createBudgetsQuery
            when debug $ putStrLn updateBudgetsQuery
            -- queries for fixed budget per row use
            let rowUsesQueries = map (\ col -> "SELECT " ++ col ++ " AS id" ++ getFromAndWhere (head tableExprData_addsOrRemoves)) provCols
            let rowUsesQuery = case rowUsesQueries of [q] -> q
                                                      qs  -> intercalate " UNION " $ map (\ q -> '(' : q ++ ")") qs
            let rowUsesCountsQuery = "SELECT sub.id AS id, count(*) as count FROM (" ++ rowUsesQuery ++ ") as sub GROUP BY sub.id"
            when useFixedBudgetPerRowUse $ do
              when debug $ putStrLn "rowUsesCountsQuery:"
              when debug $ putStrLn rowUsesCountsQuery
            let rowUsedEpsilon = "(sub.count*" ++ show epsilon_gs ++ ")"
            let rowRemainingBudget = "GREATEST(0," ++ show epsilon0 ++ " - budget)"
            let updateBudgetsQuery_gsn = "UPDATE " ++ budgetTable ++ " SET budget = budget + " ++ rowUsedEpsilon ++ " FROM (" ++ rowUsesCountsQuery ++ ") as sub WHERE " ++ budgetTable ++ ".id = sub.id"
            let updateBudgetsQuery_gsx = "UPDATE " ++ budgetTable ++ " SET (useratio,budget) = (LEAST(" ++ rowRemainingBudget ++ "," ++ rowUsedEpsilon ++ ") / " ++ rowUsedEpsilon ++
                                         ", budget + LEAST(" ++ rowUsedEpsilon ++ "," ++ rowRemainingBudget ++ ")) FROM (" ++ rowUsesCountsQuery ++ ") as sub WHERE " ++ budgetTable ++ ".id = sub.id"
            let updateBudgetsQuery_gs = if excludeExhausted args then (if oneToN args then "" else updateBudgetsQuery_gsx) else updateBudgetsQuery_gsn
            when useFixedBudgetPerRowUse $ do
              when debug $ putStrLn "updateBudgetsQuery_gs:"
              when debug $ putStrLn updateBudgetsQuery_gs
            return [createBudgetsQuery, if useFixedBudgetPerRowUse then updateBudgetsQuery_gs else updateBudgetsQuery]
        createBudgetsQueries1 <- fmap concat $ forM tablesAndAliases $ \ (tn, tas) ->
          if tn `Set.member` provenanceTablesSet
            then return []
            else do
              when debug $ printf "Table %s AS %s:\n" tn (show tas)
              createBudgetQueries (map (++ ".ID") tas) (tn ++ budgetSuffix)
        createBudgetsQueries2 <-
          if provenancesUsed
            then do
              when debug $ printf "Provenance tables:\n"
              createBudgetQueries provenanceCols provenanceBudgetTable
            else return []
        createBudgetQueries_oneton <-
          if oneToN args
            then do
              let selectedIDs = intercalate ", " $ map (\ (tn, [ta]) -> ta ++ ".ID AS " ++ ta ++ "_id") tablesAndAliases
              let isThereEnoughBudget = intercalate " AND " $ map (\ (tn, [ta]) -> "(SELECT " ++ show epsilon0 ++ " - budget FROM " ++ tn ++ budgetSuffix ++ " WHERE id = r." ++ ta ++ "_id) >= " ++ show epsilon_gs) tablesAndAliases
              let updateBudgets = concatMap (\ (tn, [ta]) -> "UPDATE " ++ tn ++ budgetSuffix ++ " SET budget = budget + " ++ show epsilon_gs ++ " WHERE id = r." ++ ta ++ "_id; ") tablesAndAliases
              let addUsedRow = "INSERT INTO " ++ usedRowsTable ++ " (" ++ intercalate ", " (map (\ (tn, [ta]) -> ta ++ "_id") tablesAndAliases)
                                                                       ++ ") VALUES (" ++ intercalate ", " (map (\ (tn, [ta]) -> "r." ++ ta ++ "_id") tablesAndAliases) ++ "); "
              let updateBudgetsQuery_gsx1n = "do $$ declare r record; begin DELETE FROM " ++ usedRowsTable ++ "; for r in SELECT " ++ selectedIDs ++ getFromAndWhere (head tableExprData_addsOrRemoves)
                    ++ " order by " ++ intercalate ", " (map (\ (tn, [ta]) -> ta ++ "_id") tablesAndAliases)
                    ++ " loop " ++
                      "if " ++ isThereEnoughBudget ++ " then " ++ updateBudgets ++ addUsedRow ++ "end if;"
                    ++ " end loop; end $$"
              when debug $ putStrLn "updateBudgetsQuery_gsx1n:"
              when debug $ putStrLn updateBudgetsQuery_gsx1n
              return [updateBudgetsQuery_gsx1n]
            else return []
        let createBudgetsQueries = createBudgetsQueries1 ++ createBudgetsQueries2 ++ createBudgetQueries_oneton

        (qmap, taskAggr, queryResult0) <-
          if useFixedBudgetPerRowUse
            then return (undefined, undefined, undefined)
            else
              if removesUsed
                then do
                  (qmapA, taskAggrA, queryResultA) <- performAnalyses args silent epsilon beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList
                                                                      tableExprData_adds attMap tableGs colTableCounts (Just addCond)
                  (qmapR, taskAggrR, queryResultR) <- performAnalyses args silent epsilon beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList
                                                                      tableExprData_removes attMap tableGs colTableCounts (Just removeCond)
                  (qmapAR, taskAggrAR, queryResultAR) <- performAnalyses args silent epsilon beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList
                                                                      tableExprData_addsOrRemoves attMap tableGs colTableCounts (Just addOrRemoveCond)
                  when debug $ printf "sum of adds = %0.6f\n" queryResultA
                  when debug $ printf "sum of removes = %0.6f\n" queryResultR
                  return (qmapAR, taskAggrAR, queryResultA - queryResultR)
                else performAnalyses args silent epsilon beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData_adds attMap tableGs colTableCounts (Just addCond)
        sendQueriesToDbAndCommit_noReplaceImproperSymbols args createBudgetsQueries

        queryResult <- if useFixedBudgetPerRowUse
          then do
            --when debug $ printf "queryResult0: %0.6f\n" queryResult0
            let createQuery = if excludeExhausted args then createQueryForExcludingRows else createQueryWithoutExcludingRows
            let query_adds = createQuery (head tableExprData_adds)
            let query_removes = createQuery (head tableExprData_removes)
            queryResultA <- sendDoubleQueryToDb args query_adds
            queryResultR <- if removesUsed then sendDoubleQueryToDb args query_removes else return 0
            when debug $ printf "query_adds: %s\n" query_adds
            when debug $ printf "sum of adds (with excluded rows) = %0.6f\n" queryResultA
            when removesUsed $ do
              when debug $ printf "query_removes: %s\n" query_removes
              when debug $ printf "sum of removes (with excluded rows) = %0.6f\n" queryResultR
            return (queryResultA - queryResultR)
          else return queryResult0

        printf "change in query result = %0.6f\n" queryResult
        noiseLevel <- if useFixedBudgetPerRowUse
          then
            if useGlobalSens args
              then return noiseLevel_gs
              else do
                -- for budget-per-row-use time series analysis. we do the combining here, not in the BanachQ module
                let args' = args { combinedSens = False }
                (_qmap, taskAggr, _queryResult) <- performAnalyses args' silent epsilon_gs beta_pru dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList
                                                                   (map addFromsAndWheresForExcludingRows tableExprData_addsOrRemoves) attMap tableGs colTableCounts (Just addOrRemoveCond)
                let (b,sensitivity) = snd $ head $ filter ((== "all input tables together") . fst) $ snd $ head $ taskAggr Map.! []
                when debug $ printf "Banach sensitivity = %0.6f\n" sensitivity
                when debug $ printf "Banach b = %0.6f\n" b
                let beta = epsilon_gs / (gamma + 1) - b
                when debug $ printf "Banach beta = %0.6f\n" beta
                let minBanachSens = exp (- beta * minG / fromIntegral (if excludeExhausted args && not (oneToN args) then length tableAliases + 1 else 1)) * maxGsens
                -- used for smoothing Banach sensitivity
                when debug $ printf "minBanachSens = %0.6f\n" minBanachSens
                let sensitivity_ls = maximum [gs_arr, sensitivity, minBanachSens]
                when debug $ printf "Combined sensitivity with local Banach sensitivity = %0.6f\n" sensitivity_ls
                let noiseLevel_ls = sensitivity_ls / b
                when debug $ printf "Noise level for combined sensitivity with local Banach sensitivity = %0.6f\n" noiseLevel_ls
                return noiseLevel_ls
          else do
            let (b,sensitivity) = snd $ head $ filter ((== "all input tables together") . fst) $ snd $ head $ taskAggr Map.! []
            when debug $ printf "sensitivity = %0.6f\n" sensitivity
            when debug $ printf "b = %0.6f\n" b
            let beta = epsilon / (gamma + 1) - b
            when debug $ printf "beta = %0.6f\n" beta
            let noiseLevel = sensitivity / b
            return noiseLevel
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
    if combinedSens args
      then do
        let totalAllowedEpsilon = if useFixedBudgetPerRowUse then max epsilon0 (epsilon_gs * fromIntegral (maxBudgetUses args time))
                                               else epsilon * fromIntegral (maxBudgetTimeperiods args time)
        when debug $ printf "total epsilon used so far = %0.6f (private)\n" totalUsedEpsilon
        printf "total epsilon allowed so far = %0.6f (public)\n" totalAllowedEpsilon
        when debug $ when (totalUsedEpsilon > totalAllowedEpsilon + (if useFixedBudgetPerRowUse then epsilon_gs else epsilon)*0.5) $ putStrLn "PRIVACY LEAK: budget exceeded, DP not guaranteed anymore (and this message leaks further)"
      else
        printf "total epsilon used so far = %0.6f\n" totalUsedEpsilon

    printf "Query result at time point #%d = r[%d]\n" time time
    printf "r[%d] = %s\n" time (intercalate " + " $ map (\ (t1,t2,val,nl) -> printf "x[%d-%d]" t1 t2) releases')
    forM_ releases' $ \ (t1,t2,val,nl) -> printf "x[%d-%d] = %0.6f ± %0.6f\n" t1 t2 val nl
    let (_,_,vals,nls) = unzip4 releases'
    let val = sum vals
    let nl = sqrt (sum (map (^2) nls))
    printf "r[%d] = %0.6f ± %0.6f\n" time val nl

    return (time,state'',releases')) (0::Int,[(0,0)],[]) ((case maxTimepoints args of Just n -> take n; Nothing -> id) $ lines contents)

  return ()
