module Preprocess where

import Debug.Trace

import Data.Bits
import Data.Char
import Data.Either
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Void

-- import Expr directly from Banach.hs, 'qualified' because we want to reuse the names
import qualified Banach as B
import Aexpr
import ErrorMsg
import Expr
import Norms
import Query

type TableName  = String
type TableAlias = String

-- we agree that this key will be used for the output query if not specified otherwise
defaultOutputTableName :: String
defaultOutputTableName = "output"

-------------------------------------------------------
---- Converting a Query to Banach Analyser input   ----
-------------------------------------------------------

-- the format of the query
--   "[String]"         is the list of columns by which the result should be grouped
--   "[Function]"       is the list of the queried function itself (SELECT x)
--   "[TableName]"      is the list of input tables that are used in the query (FROM x)
--   "[TableAlias]"     is the list of table names that are used in the query (FROM ... AS x)
--   "[Function]"       is the list of filters used in the query (WHERE x)
data Query
  = P [String] [Function] (M.Map TableAlias TableName) [Function]
  deriving (Show)

data TableData =
    -- content columnNames exprs norms aggrNorms sensRows sensCols originalTablename 
    T B.Table [VarName] Function [[Int]] [VarName] TableName
  deriving Show

getTableValues   (T x _ _ _ _ _) = x
getColNames      (T _ x _ _ _ _) = x
getNorm          (T _ _ x _ _ _) = x
getSensitiveRows (T _ _ _ x _ _) = x
getSensitiveCols (T _ _ _ _ x _) = x
getTableName     (T _ _ _ _ _ x) = x

getQueryGroupNames (P x _ _ _) = x
getQueryFunctions  (P _ x _ _) = x
getQueryAliasMap   (P _ _ x _) = x
getQueryFilters    (P _ _ _ x) = x

-- read the database from the file as a matrix of doubles
-- read is as a single table row
readDB :: String -> IO ([VarName], B.Table)
readDB dbFileName = do
    (firstLine:ls) <- fmap lines (readInput dbFileName)
    let varNames = words firstLine
    let table    = readDoubles (foldr (\x y -> x ++ "\n" ++ y) "" ls)
    return (varNames, table)

query2Expr :: (M.Map VarName B.Var) -> (S.Set B.Var) -> Function -> (S.Set B.Var, B.Expr)
query2Expr inputMap sensitiveColSet (F asgnMap y) =
    let x = extractArg y in
    let (_,expr') = matchAsgnVariable "" queryExpression inputMap asgnMap x in
    let (usedSensCols,expr) = markExprCols sensitiveColSet expr' in
    (S.fromList usedSensCols, expr)

queryExprAggregate :: Function-> B.Expr -> B.TableExpr
queryExprAggregate (F _ y) z =
    queryArg y [z]

queryExprAggregateSensRows :: Int -> [Bool] -> Function-> B.Expr -> B.TableExpr
queryExprAggregateSensRows numOfRows sensitiveRowsCV  (F _ y) z = 
    let zs = zipWith (\x y -> if x then y else B.ZeroSens y) sensitiveRowsCV (replicate numOfRows z) in
    queryArg y zs

norm2Expr :: (Show a, Ord a) => String -> (M.Map VarName a) -> Function -> (Norm a, ADouble)
norm2Expr prefix inputMap (F asgnMap y) =
    let x = extractArg y in
    let (_,z) = matchAsgnVariable prefix normExpression inputMap asgnMap x in
    (z, normArg y)

processExpression :: (Show a, Ord a) => 
                     String ->                                 -- the name of the database file that we prepend to all variable names
                     (Expr -> [a] -> [b] -> [S.Set a] -> b) -> -- the function that actually rewrites the term
                     (M.Map VarName a) ->                      -- input variable map
                     (M.Map VarName Expr) ->                   -- assigmnent variable map
                     Expr ->                                   -- the expression that we rewrite
                     (S.Set a, b)
processExpression s f inputMap asgnMap expr =
    let varNames = extractArgs expr in
    let usedInputVarNames = filter (\x -> M.member (s ++ x) inputMap) varNames in
    let usedAsgnVarNames  = filter (\x -> M.member x asgnMap)  varNames in

    let inputVars        = map (\x -> inputMap ! (s ++ x)) usedInputVarNames in
    let asgnInputsExprs  = map (matchAsgnVariable s f inputMap asgnMap) usedAsgnVarNames in

    let (asgnInputs,asgnExprs) = unzip asgnInputsExprs in
    (S.union (S.fromList inputVars) (foldr S.union S.empty asgnInputs), f expr inputVars asgnExprs asgnInputs)

--check if the variable is a keys in a map, apply processExpression to the value of that key
matchAsgnVariable :: (Show a, Ord a) => String -> (Expr -> [a] -> [b] -> [S.Set a] -> b) -> (M.Map VarName a) -> (M.Map VarName Expr) -> VarName -> (S.Set a,b)
matchAsgnVariable s f inputMap asgnMap x =

        -- if y is an assignment variable, find its value recursively
        let expr = (asgnMap ! x) in
        processExpression s f inputMap asgnMap expr

-- read the DB line by line -- no speacial parsing, assume that the delimiters are whitespaces
readInput :: String -> IO String
readInput path = do
   content <- readFile path
   return content

readEither :: (Read a) => String -> Either a String
readEither s = case reads s of
              [(x, "")] -> Left x
              _ -> Right s

-- djb2 hash
hash :: String -> Double
hash = fromIntegral . foldl' (\h c -> xor (33*h) (ord c)) 5381

-- tries to read an integer, then a boolean, and if fails, returns the hash of the input string
readIntBoolString :: String -> Double
readIntBoolString s =
    let a = readEither s :: Either Double String in
    case a of
        Left  x -> x
        Right x ->
            let b = readEither s :: Either Bool String in
            case b of
                Left  x -> fromIntegral $ fromEnum x
                Right x -> hash s

readDoubles :: String -> [[Double]]
readDoubles s = fmap (map readIntBoolString . words) (lines s)

concatMaps :: (Ord k) => [M.Map k a] -> M.Map k a
concatMaps xs = foldr M.union M.empty xs

-- add all the queries of entire list qs2 to each query of the list qs1
mergeQueryFuns :: [Function] -> [Function] -> [Function]
mergeQueryFuns [] _ = []
mergeQueryFuns (F as b : qs1) qs2 =
    let as2 = concatMaps $ map (\(F as1 _) -> as1) qs2 in
    (F (M.union as as2) b) : (mergeQueryFuns qs1 qs2)

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

-- compute table data for a cross product
getTableCrossProductData :: [TableAlias] -> M.Map TableAlias TableData -> (B.Table, [[Int]], [VarName], [VarName])
getTableCrossProductData tableAliases tableMap =

    let allInputVars     = map (getColNames .      (tableMap ! ) ) tableAliases in
    let allSensitiveVars = map (getSensitiveCols . (tableMap ! ) ) tableAliases in
    let allTables        = map (getTableValues .   (tableMap ! ) ) tableAliases in
    let allSensitiveRows = map (getSensitiveRows . (tableMap ! ) ) tableAliases in

    -- the input variables are concatenated in the order of tables, since each of them describes a column
    let inputVarList     = concat allInputVars in
    let sensitiveVarList = concat allSensitiveVars in

    -- find the cross product of all used tables
    let crossProductTable = tableJoin allTables in

    -- find the cross product of table row indices to remeber which row has come from which table
    let sensitiveRowCrossProduct = vectorJoin allSensitiveRows in

    (crossProductTable, sensitiveRowCrossProduct, inputVarList, sensitiveVarList)

processAllTables :: [TableAlias] -> [TableName] -> [[VarName]] -> [B.Table] -> [Function] -> [[VarName]] -> [[Int]] -> [(TableAlias, TableData)]
processAllTables [] [] [] [] [] [] [] = []
processAllTables (tableAlias:xs0) (x1:xs1) (x2:xs2) (x3:xs3) (x4:xs4) (x5:xs5) (x6:xs6) =
    let tableData = processOneTable tableAlias x1 x2 x3 x4 x5 x6 in
    (tableAlias,tableData) : (processAllTables xs0 xs1 xs2 xs3 xs4 xs5 xs6)

processOneTable :: TableAlias -> TableName -> [VarName] -> B.Table -> Function -> [VarName] -> [Int] -> TableData
processOneTable tableAlias tableName inputVars tableValues normFun dbSensitiveVars dbSensitiveRows =

    -- let non-sensitive rows be indexed by -1
    let numOfRows             = length tableValues in
    let extendedSensitiveRows = map (\x -> [x]) $ fillMissingWith (-1) numOfRows dbSensitiveRows in

    T tableValues inputVars normFun extendedSensitiveRows dbSensitiveVars tableName


deriveExprNorm :: Bool -> Bool -> Int -> (M.Map VarName B.Var) -> S.Set B.Var -> [TableAlias] -> [Function] -> B.Expr -> B.TableExpr -> B.TableExpr
deriveExprNorm debug usePrefices numOfSensRows inputMap sensitiveCols dbNormTableAliases dbNormFuns queryExpr queryAggr =

    let namePrefices = map (\tableAlias -> if usePrefices then tableAlias ++ "." else "") dbNormTableAliases in
    let (dbNorms1,dbAggrNorms) = unzip $ zipWith (\x y -> norm2Expr x inputMap y) namePrefices dbNormFuns in
    let dbNorms = map (markNormCols sensitiveCols) dbNorms1 in

    -- if there are several tables, we assume that we compute sensitivity w.r.t. max of them
    -- alternatively, we could assign different sensitivity weights to different tables
    let dbExprNorm = NormL Any dbNorms in
    let dbAggrNorm = foldr takeFiner (Exactly 1.0) dbAggrNorms in

    let orderedVars = [0..M.size inputMap - 1] in
    let queryExprNorm = deriveNorm orderedVars queryExpr in
    let queryAggrNorm = deriveTableNorm queryAggr in

    -- adjust the query norm to the table norm
    let (mapCol,mapLN) = normalizeAndVerify queryExprNorm dbExprNorm in
    let adjustedQuery = updateTableExpr queryAggr mapCol mapLN queryAggrNorm dbAggrNorm numOfSensRows in

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


filteredExpr :: B.Table -> (M.Map VarName B.Var) -> [[Int]] -> S.Set B.Var -> [Function] -> [Function] -> ([Function], [[Int]], B.Table)
filteredExpr table inputMap sensRowMatrix sensitiveCols filterFuns queryFuns =

    let numOfRows = length table in

    -- collect sensitive variables used by each filter, compute all values upon which a filter makes its decision about a row
    let (filterSensVars, filterExprs) = unzip $ map (query2Expr inputMap sensitiveCols) filterFuns in
    let filterValues  = map (\x -> map B.fx $ zipWith B.analyzeExpr table (replicate numOfRows x)) filterExprs in

    -- we start from all-True filter, and map bad rows to False
    let initialFilter = replicate numOfRows True in

    let (filteredQueryFuns,goodRows) = applyFilters initialFilter queryFuns sensRowMatrix filterFuns filterSensVars filterValues in
    let (filteredTable, filteredSensRowMatrix, _) = unzip3 $ filter (\(x,y,b) -> b) (zip3 table sensRowMatrix goodRows) in
    (filteredQueryFuns, filteredSensRowMatrix, filteredTable)

-- construct input for multitable Banach analyser
-- we read the columns in the order they are given in allTableNorms, since it matches the cross product table itself
inputWrtEachTable   :: Bool -> Bool -> [TableAlias] -> B.Expr -> B.Expr -> B.TableExpr -> [[Int]] ->
                      (M.Map VarName B.Var) -> (M.Map TableAlias TableData) -> [(TableName, TableAlias, [Int], B.TableExpr, B.TableExpr,B.TableExpr)]
inputWrtEachTable _ _ _ _ _ _ [] _ _ = error $ error_emptyTable
inputWrtEachTable debug usePrefices tableAliases minmaxQueryExpr queryExpr queryAggr sensitiveRowMatrix inputMap tableMap =
    let sensitiveRowMatrixColumns = transpose sensitiveRowMatrix in
    let n1 = length sensitiveRowMatrixColumns in
    let n2 = length tableAliases in
    if n1 /= n2 then error $ error_internal_sensitivityMatrix n1 n2 else
    inputWrtEachTableRec debug usePrefices tableAliases minmaxQueryExpr queryExpr queryAggr sensitiveRowMatrixColumns inputMap tableMap

inputWrtEachTableRec :: Bool -> Bool -> [TableAlias] -> B.Expr -> B.Expr -> B.TableExpr -> [[Int]] ->
                       (M.Map VarName B.Var) -> (M.Map TableAlias TableData) -> [(TableName, TableAlias, [Int], B.TableExpr, B.TableExpr, B.TableExpr)]
inputWrtEachTableRec _ _ [] _ _ _ _ _ _ = []
inputWrtEachTableRec debug usePrefices (tableAlias : ts) minmaxQueryExpr queryExpr queryAggr (col:cols) inputMap tableMap =

    let tableData     = tableMap ! tableAlias in

    let tableNorm     = getNorm          tableData in
    let tableName     = getTableName     tableData in
    let tableSensVars = getSensitiveCols tableData in
    let tableSensCols = S.fromList $ map (inputMap ! ) tableSensVars in

    let newQueryExpr = snd $ markExprCols      tableSensCols queryExpr in
    let newQueryAggr =       markTableExprCols tableSensCols queryAggr in

    -- these subqueries are needed to compute aggregates that will be used for _filtered_ MIN and MAX
    let minmaxNewQueryExpr = snd $ markExprCols      tableSensCols minmaxQueryExpr in
    let minQueryAggr       = B.SelectMin [minmaxNewQueryExpr] in
    let maxQueryAggr       = B.SelectMax [minmaxNewQueryExpr] in

    let numOfRows = length col in
    let numOfSensRows = length $ filter (>= 0) col in

    traceIfDebug debug ("num of rows: " ++ show numOfRows) $
    traceIfDebug debug ("num of Sens rows: " ++ show numOfSensRows) $

    let adjustedMinQuery = deriveExprNorm debug usePrefices numOfSensRows inputMap tableSensCols [tableAlias] [tableNorm] minmaxNewQueryExpr minQueryAggr in
    let adjustedMaxQuery = deriveExprNorm debug usePrefices numOfSensRows inputMap tableSensCols [tableAlias] [tableNorm] minmaxNewQueryExpr maxQueryAggr in

    let adjustedQuery    = deriveExprNorm debug usePrefices numOfSensRows inputMap tableSensCols [tableAlias] [tableNorm] newQueryExpr newQueryAggr in
    (tableName, tableAlias, col, adjustedQuery, adjustedMinQuery, adjustedMaxQuery) : inputWrtEachTableRec debug usePrefices ts minmaxQueryExpr queryExpr queryAggr cols inputMap tableMap

-- as in the old solution, this declares a join row sensitive iff at least one of participating rows is sensitive 
-- we use the structure that marks all insensitive entries with '-1'
sensitiveOR :: [[Int]] -> [Bool]
sensitiveOR [] = []
sensitiveOR (row:rows) =
    let rowSet = S.fromList row in
    if S.member (-1) rowSet then False : sensitiveOR rows
    else True : sensitiveOR rows

-- this outputs a trace message only if the flag debug=True is set
traceIfDebug :: Bool -> String -> (a -> a)
traceIfDebug debug msg =
    if debug then trace msg
    else id

traceIOIfDebug :: Bool -> String -> IO ()
traceIOIfDebug debug msg = do
    if debug then traceIO msg
    else return ()

updateVariableNames :: TableAlias -> Function -> Function
updateVariableNames prefix (F as b) =
    let as' = M.map (updatePreficesExpr prefix) $ M.mapKeys (updatePrefices prefix) as in
    let b'  = updatePreficesTableExpr prefix b in
    F as' b'

processQuery :: TableName -> (M.Map TableName Query) -> TableName -> TableAlias -> TableName -> ([[TableName]], [TableAlias],[TableName], [Function], [Function])
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
        let prefix = if tableAlias == outputTableName then "" else tableAlias ++ "." in

        let newQueryFuns    = map (updateVariableNames prefix) queryFuns in
        let newFilterFuns   = map (updateVariableNames prefix) filterFuns in

        let newSubQueryFuns = map (updateVariableNames prefix) subQueryFuns in
        let newSubFiltFuns  = map (updateVariableNames prefix) subFiltFuns in

        -- put all subquery funs and all filters together with the current query's funs and filters
        let outputQueryFuns = mergeQueryFuns newQueryFuns newSubQueryFuns in
        let outputFilters   = newSubFiltFuns ++ mergeQueryFuns newFilterFuns newSubQueryFuns in

        (map (taskName :) taskNames, map (prefix ++) tableAliases, tableNames, outputQueryFuns, outputFilters)

