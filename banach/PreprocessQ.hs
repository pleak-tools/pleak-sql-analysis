module PreprocessQ where

import Debug.Trace

import Control.Monad (when)
import Data.Either
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Void
import ProgramOptions

-- import Expr directly from Banach.hs, 'qualified' because we want to reuse the names
import qualified Banach as B
import qualified BanachQ as BQ
import qualified DatabaseQ as DQ
import AexprQ
import ErrorMsg
import ExprQ
import NormsQ
import ParserQ
import QueryQ
import ReaderQ


-- this outputs a trace message only if the flag debug=True is set
traceIfDebug :: Bool -> String -> (a -> a)
traceIfDebug debug msg =
    if debug then trace msg
    else id

traceIOIfDebug :: Bool -> String -> IO ()
traceIOIfDebug debug msg = do
    if debug then traceIO msg
    else return ()

-------------------------------------------------------
---- Converting a Query to Banach Analyser input   ----
-------------------------------------------------------

norm2Expr :: (Show a, Ord a) => String -> (M.Map VarName a) -> NormFunction -> (Norm a, ADouble)
norm2Expr prefix inputMap (NF asgnMap y) =
    let x = extractArg y in
    let (_,z) = matchAsgnVariable prefix inputMap asgnMap x in
    (z, normArg y)

processExpression :: (Show a, Ord a) => 
                     String ->                                 -- the name of the database file that we prepend to all variable names
                     (M.Map VarName a) ->                      -- input variable map
                     (M.Map VarName Expr) ->                   -- assigmnent variable map
                     Expr ->                                   -- the expression that we rewrite
                     (S.Set a, Norm a)
processExpression s inputMap asgnMap expr =
    let varNames = extractArgs expr in
    let usedInputVarNames = filter (\x -> M.member (s ++ x) inputMap) varNames in
    let usedAsgnVarNames  = filter (\x -> M.member x asgnMap)  varNames in

    let inputVars        = map (\x -> inputMap ! (s ++ x)) usedInputVarNames in
    let asgnInputsExprs  = map (matchAsgnVariable s inputMap asgnMap) usedAsgnVarNames in

    let (asgnInputs,asgnExprs) = unzip asgnInputsExprs in
    (S.union (S.fromList inputVars) (foldr S.union S.empty asgnInputs), normExpression expr inputVars asgnExprs asgnInputs)

--check if the variable is a keys in a map, apply processExpression to the value of that key
matchAsgnVariable :: (Show a, Ord a) => String -> (M.Map VarName a) -> (M.Map VarName Expr) -> VarName -> (S.Set a, Norm a)
matchAsgnVariable s inputMap asgnMap x =

        -- if y is an assignment variable, find its value recursively
        let expr = (asgnMap ! x) in
        processExpression s inputMap asgnMap expr

-------------------------------------------
---- Extraction of table information   ----
-------------------------------------------

-- substitute expressions of fs into aexpr
mergeQueryFuns :: [Function] -> AExpr VarName -> AExpr VarName
mergeQueryFuns fs aexpr =
    let aexprMap = M.fromList $ map (\(F aexpr2 b) -> (extractArg b,aexpr2)) fs in
    aexprSubstitute aexprMap aexpr

-- this checks that the subqueries are all of select-type
badQFuns :: [Function] -> (Bool, String)
badQFuns [] = (False,"")
badQFuns (F _ b : qs) =
    case b of
        Select _ -> badQFuns qs
        _        -> (True, error_queryExpr_aggrInterm b)

fillMissingWith :: Int -> Int -> [Int] -> [Int]
fillMissingWith y n xs  = fillMissingWithRec xs y n 0

fillMissingWithRec [] y n i = replicate (n-i) y
fillMissingWithRec (x:xs) y n i =
    if (i == n) then []
    else if (x == i) then x : fillMissingWithRec xs y  n(i+1)
    else if (x > i) then y : fillMissingWithRec (x:xs) y n (i+1)
    else error $ error_internal_fillMissing x i xs


processAllTables :: [TableAlias] -> [TableName] -> [[VarName]] -> [B.Table] -> [NormFunction] -> [[VarName]] -> [[Int]] -> [(TableAlias, TableData)]
processAllTables [] [] [] [] [] [] [] = []
processAllTables (tableAlias:xs0) (x1:xs1) (x2:xs2) (x3:xs3) (x4:xs4) (x5:xs5) (x6:xs6) =
    let tableData = processOneTable tableAlias x1 x2 x3 x4 x5 x6 in
    (tableAlias,tableData) : (processAllTables xs0 xs1 xs2 xs3 xs4 xs5 xs6)

processOneTable :: TableAlias -> TableName -> [VarName] -> B.Table -> NormFunction -> [VarName] -> [Int] -> TableData
processOneTable tableAlias tableName inputVars tableValues normFun dbSensitiveVars dbSensitiveRows =

    -- let non-sensitive rows be indexed by -1
    let numOfRows             = length tableValues in
    let extendedSensitiveRows = map (\x -> [x]) $ fillMissingWith (-1) numOfRows dbSensitiveRows in

    T tableValues inputVars normFun extendedSensitiveRows dbSensitiveVars tableName

deriveExprNorm :: Bool -> Int -> (M.Map VarName B.Var) -> S.Set B.Var -> [TableAlias] -> [NormFunction] -> B.Expr -> B.TableExpr -> B.TableExpr
deriveExprNorm debug numOfRows inputMap sensitiveCols dbNormTableAliases dbNormFuns queryExpr queryAggr =

    let namePrefices = map (\tableAlias -> tableAlias ++ ".") dbNormTableAliases in
    let (dbNorms1,dbAggrNorms) = unzip $ zipWith (\x y -> norm2Expr x inputMap y) namePrefices dbNormFuns in
    let dbNorms = map (markNormCols sensitiveCols) dbNorms1 in

    -- if there are several tables, we assume that we compute sensitivity w.r.t. max of them
    -- alternatively, we could assign different sensitivity weights to different tables
    let dbExprNorm = NormL Any dbNorms in
    let dbAggrNorm = foldr takeFiner (Exactly 1.0) dbAggrNorms in

    let orderedVars = [0..M.size inputMap - 1] in
    let queryExprNorm = deriveNorm orderedVars queryExpr in
    let queryAggrNorm = deriveTableNorm queryAggr in

    -- adjust the query to the database norm
    let (mapCol,mapLN) = normalizeAndVerify queryExprNorm dbExprNorm in
    let adjustedQuery = updateTableExpr numOfRows queryAggr mapCol mapLN queryAggrNorm dbAggrNorm in

    let newQueryNorm = deriveNorm orderedVars $ head (getExprFromTableExpr adjustedQuery) in
    let newAggrNorm  = deriveTableNorm adjustedQuery in

    traceIfDebug debug ("----------------") $
    traceIfDebug debug (show dbAggrNorms) $
    traceIfDebug debug ("database norm     = Rows: " ++ show dbAggrNorm    ++ " | Cols: "  ++ show (normalizeNorm dbExprNorm)) $
    traceIfDebug debug ("intial query norm = Rows: " ++ show queryAggrNorm ++ " | Cols: "  ++ show (normalizeNorm queryExprNorm)) $
    traceIfDebug debug ("adjust query norm = Rows: " ++ show newAggrNorm   ++ " | Cols: "  ++ show (normalizeNorm newQueryNorm)) $
    traceIfDebug debug ("scaling: " ++ show mapCol ++ "\n\t " ++ show mapLN ++ "\n\n") $
    traceIfDebug debug ("----------------") $
    adjustedQuery


-- construct input for multitable Banach analyser
-- we read the columns in the order they are given in allTableNorms, since it matches the cross product table itself
inputWrtEachTable   :: Bool -> (M.Map VarName B.Var) -> (S.Set B.Var) ->
                       [TableAlias] -> B.TableExpr -> (String,String,String) -> Int -> (M.Map TableAlias TableData) ->
                       [(TableName, B.TableExpr, String)]
inputWrtEachTable _ _ _ [] _ _ _ _ = []
inputWrtEachTable debug inputMap allSensCols (tableAlias : ts) filtQuery (sel,fr,wh) numOfRows tableMap =

    let tableData     = tableMap ! tableAlias in

    let tableNorm     = getNorm          tableData in
    let tableName     = getTableName     tableData in
    let tableSensVars = getSensitiveCols tableData in
    let tableSensCols = S.fromList $ map (inputMap ! ) tableSensVars in

    -- now transform the main query to a banach expression, now it is fine to use only the current table's sensitive columns
    let (queryExpr,  queryAggr)  = insertZeroSens tableSensCols filtQuery in

    -- the query will also take into account sensitive rows of the current sensitive table
    --let uniqueInputTableNames = S.toList $ S.fromList (map getTableName (M.elems tableMap)) in
    let usedTables    = map (\(x,y) -> let z = getTableName y in if x == z then z else z ++ " AS " ++ x) (M.toList tableMap) in
    let sensRowTable  = tableName ++ "_sensRows" in
    let sensRowFilter = tableName ++ "_sensRows.ID = " ++ tableAlias ++ ".ID" in

    -- a query that creates the large cross product table
    let fr1  = fr ++ ", " ++ sensRowTable in
    let wh1  = wh ++ " AND " ++ sensRowFilter in
    let sqlQuery = sel ++ fr1 ++ wh1 in

    -- the query expressions defined over the large cross product table
    let adjTableExpr = deriveExprNorm debug numOfRows inputMap tableSensCols [tableAlias] [tableNorm] queryExpr queryAggr in

    (tableName, adjTableExpr, sqlQuery) : inputWrtEachTable debug inputMap allSensCols ts filtQuery (sel,fr,wh) numOfRows tableMap


processQuery :: TableName -> (M.Map TableName Query) -> TableName -> TableAlias -> TableName -> ([[TableName]], [TableAlias],[TableName], [Function], [AExpr VarName])
processQuery outputTableName queryMap taskName tableAlias tableName =

    -- if the table is not in the query map, then it is an input table
    if not (M.member tableName queryMap) then
        ([[taskName]], [tableAlias], [tableName], [], [])
    else
        -- collect all used tables of this query
        let query@(P groupColnames queryFuns usedAliasMap filterFuns) = queryMap ! tableName in

        -- we do not support 'group by' yet
        if length groupColnames > 0 then error $ error_queryExpr_groupBy else

        -- the subqueries should be of select-type
        let (iserr, err) = badQFuns queryFuns in
        if tableAlias /= outputTableName && iserr then error $ err else

        -- recursively, collect all subqueries and filters used to generate all used tables
        let usedAliases = M.keys usedAliasMap in
        let subData = map (\key -> processQuery outputTableName queryMap tableName key (usedAliasMap ! key)) usedAliases in
        let (taskNames', tableAliases', tableNames', subQueryFuns', subFiltFuns') = unzip5 subData in

        let taskNames     = concat taskNames'    in
        let tableAliases  = concat tableAliases' in
        let tableNames    = concat tableNames'   in
        let subQueryFuns  = concat subQueryFuns' in
        let subFiltFuns   = concat subFiltFuns'  in

        -- add the current table alias as a prefix to all variables in all queries and filters
        let prefix = if tableAlias == outputTableName then "" else tableAlias ++ "_" in
        let fullTablePaths = S.fromList tableAliases in
        let newQueryFuns    = map (updateQueryVariableNames fullTablePaths prefix) queryFuns in
        let newFilterFuns   = map (updateFilterVariableNames fullTablePaths prefix) filterFuns in

        let newSubQueryFuns = map (updateQueryVariableNames fullTablePaths prefix) subQueryFuns in
        let newSubFiltFuns  = map (updateFilterVariableNames fullTablePaths prefix) subFiltFuns in

        -- put all subquery funs and all filters together with the current query's funs and filters
        let outputQueryFuns = map (\ (F qaexpr b) -> F (mergeQueryFuns newSubQueryFuns qaexpr) b) newQueryFuns in
        let outputFilters   = newSubFiltFuns ++ map (mergeQueryFuns newSubQueryFuns) newFilterFuns in

        (map (taskName :) taskNames, map (prefix ++) tableAliases, tableNames, outputQueryFuns, outputFilters)


-- assume that the tables are located in the same place where the query is
readAllTables :: String -> [TableName] -> [TableAlias] -> IO (M.Map TableAlias TableData)
readAllTables queryPath tableNames tableAliases = do

    -- collect all tables and all column names that will be used in our query
    -- read table sensitivities from corresponding files
    -- mapM is a standard function [IO a] -> IO [a]
    let dbData     = mapM (\tableName -> readDB            $ queryPath ++ tableName ++ ".db")  tableNames
    let dbNormData = mapM (\tableName -> parseNormFromFile $ queryPath ++ tableName ++ ".nrm") tableNames

    (tableColNames,  tableValues)   <- fmap unzip dbData
    (tableSensitives,tableNormFuns) <- fmap unzip dbNormData
    let (tableSensitiveRows,tableSensitiveVars) = unzip tableSensitives

    -- we put table names in front of column names
    let namePrefices = map (\tableAlias -> tableAlias ++ ".") tableAliases
    let taggedTableColNames = zipWith (\x ys -> map (\y -> x ++ y) ys) namePrefices tableColNames
    let taggedSensitiveVars = zipWith (\x ys -> map (\y -> x ++ y) ys) namePrefices tableSensitiveVars

    -- put all table data together
    let tableMap = processAllTables tableAliases tableNames taggedTableColNames tableValues tableNormFuns taggedSensitiveVars tableSensitiveRows
    return (M.fromList tableMap)


-- putting everything together
--getBanachAnalyserInput :: String -> IO (B.Table, B.TableExpr)
getBanachAnalyserInput :: Bool -> String -> IO ([String], [(TableName, B.TableExpr,String)])
getBanachAnalyserInput debug input = do

    putStrLn $ "\\echo ##========== Query " ++ input ++ " ==============="
    let queryPath = reverse $ dropWhile (/= '/') (reverse input)

    -- "sqlQuery" parses a single query of the form SELECT ... FROM ... WHERE
    (outputTableName,queryMap) <- parseSqlQueryFromFile input

    -- extract the tables that should be read from input files, take into account copies
    -- substitute intermediate queries into the aggregated query
    let (taskNames, inputTableAliases, inputTableNames, outputQueryFuns, filterAexprs) = processQuery outputTableName queryMap "" outputTableName outputTableName

    let indexedTaskNames = zip taskNames [0..(length taskNames) - 1]
    let taskMaps = concat $ map (\(ts,i) -> (map (\t -> (t,[i])) ) ts) indexedTaskNames
    let taskMap  = M.toList $ M.fromListWith (++) $ filter (\(t,_) -> t /= "") taskMaps

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Input table names:   " ++ show inputTableNames
    traceIOIfDebug debug $ "Input table aliases: " ++ show inputTableAliases
    traceIOIfDebug debug $ "Task names:          " ++ show taskNames
    traceIOIfDebug debug $ "Task map:            " ++ show taskMap

    --traceIOIfDebug debug $ "----------------"
    --traceIOIfDebug debug $ "TableQ " ++ show outputQueryFuns
    --traceIOIfDebug debug $ "TableF " ++ show outputFilterFuns

    -- inputTableMap maps input table aliases to the actual table data that it reads from file (table contents, column names, norm, sensitivities)
    inputTableMap <- readAllTables queryPath inputTableNames inputTableAliases

    -- the columns of the cross product are ordered according to "M.keys inputTableMap"
    let (colNames, sensitiveVarList) = getAllColumns inputTableMap

    -- assign a unique integer to each column name, which is the order of this column in the cross product table
    let inputMap        = M.fromList $ zip colNames [0..length colNames - 1]
    let sensitiveColSet = S.fromList $ map (inputMap ! ) sensitiveVarList

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "All input variables:    " ++ show (M.toList inputMap)
    traceIOIfDebug debug $ "All sensitive cols:     " ++ show sensitiveColSet

    -- we assume that the output query table has only one column
    when (length outputQueryFuns > 1) $ error $ error_queryExpr_singleColumn
    let outputQueryFun  = head outputQueryFuns
    let queryStr = queryToString outputQueryFun

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Query fun  (w/o filter) = " ++ show queryStr
    traceIOIfDebug debug $ "Number of Filters:" ++ show (length filterAexprs)
    traceIOIfDebug debug $ "Filters:" ++ show filterAexprs
    traceIOIfDebug debug $ "----------------"
    
    -- we filter out rows using globally public filters, since different filterings would be bad for combined sensitivity over all tables
    let filterSensVars = map (\x -> S.intersection sensitiveColSet (aexprToColSet inputMap x)) filterAexprs
    let (filtQueryFuns, pubFilterAexprs) = addFiltersToQueries [outputQueryFun] filterAexprs filterSensVars
    let filtQueryFun = head filtQueryFuns
    let (queryExpr,queryAggr,filtQueryStr) = queryToExpr inputMap sensitiveColSet filtQueryFun
    let pubFilter  = map aexprToString pubFilterAexprs

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Public filter: " ++ show pubFilter
    traceIOIfDebug debug $ "Query with private filters: " ++ filtQueryStr
    traceIOIfDebug debug $ "filterSensVars: " ++ show filterSensVars

    -- a query that creates the large cross product table
    let usedTables    = map (\(x,y) -> let z = getTableName y in if x == z then z else z ++ " AS " ++ x) (M.toList inputTableMap)
    let sel = "SELECT " ++ intercalate ", " colNames
    let fr  = " FROM "  ++ intercalate ", " usedTables
    let wh  = " WHERE " ++ (if length pubFilter == 0 then "true" else intercalate " AND " pubFilter)

    args <- getProgramOptions

    -- compute the number of rows using sel, fr, wh
    let numOfRowsQuery = "SELECT COUNT(*)" ++ fr ++ wh
    traceIOIfDebug debug $ "--Num_of_rows--------------"
    traceIOIfDebug debug $ numOfRowsQuery
    numOfRows <- DQ.sendDoubleQueryToDb args numOfRowsQuery

    -- compute min/max queries using sel, fr, wh
    let minExprQuery = "SELECT MIN(" ++ queryStr ++ ")" ++ fr ++ wh
    let maxExprQuery = "SELECT MAX(" ++ queryStr ++ ")" ++ fr ++ wh
    traceIOIfDebug debug $ "--Min--------------"
    traceIOIfDebug debug $ minExprQuery
    traceIOIfDebug debug $ "--Max--------------"
    traceIOIfDebug debug $ maxExprQuery
    arMin <- DQ.sendDoubleQueryToDb args minExprQuery
    arMax <- DQ.sendDoubleQueryToDb args maxExprQuery

    -- replace ARMin and ARMax inside the queries with actual precomputed data
    let finalTableExpr = applyPrecAggrTable arMin arMax queryAggr

    --bring the input to the form [(TableName, TableExpr, QueryString)]
    let dataWrtEachTable = inputWrtEachTable debug inputMap sensitiveColSet (M.keys inputTableMap) finalTableExpr (sel,fr,wh) (round numOfRows) inputTableMap
    let (allTableNames, finalTableExpr, sqlQueries) = unzip3 dataWrtEachTable

    -- the first column now always marks sensitive rows
    let extColNames = colNames ++ ["sensitive"]
    let tableExprData = (extColNames, zip3 allTableNames finalTableExpr sqlQueries)

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "tableExprData:" ++ show tableExprData
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "queries: " ++ show sqlQueries
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "column names: " ++ show extColNames
    traceIOIfDebug debug $ "----------------"

    -- return data to the banach space analyser
    return tableExprData

