module PreprocessQ where

---------------------------------------------------------
---- This module preprocesses a Query
----  and prepares it for Banach Analyser input
---------------------------------------------------------

import Debug.Trace

import Control.Monad (when, zipWithM, forM)
import Data.Char
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
import CreateTablesQ
import DatabaseQ
import ErrorMsg
import ExprQ
import GroupQ
import NormsQ
import ParserQ
import PolicyQ
import ProgramOptions
import QueryQ
import ReaderQ
import SchemaQ
import SelectQueryQ

-- this outputs a trace message only if the flag debug=True is set
traceIfDebug :: Bool -> String -> (a -> a)
traceIfDebug debug msg =
    if debug then trace msg
    else id

traceIOIfDebug :: Bool -> String -> IO ()
traceIOIfDebug debug msg = do
    if debug then traceIO msg
    else return ()

-- different types of queries
isAggrQuery   (F _ b) = case b of {SelectPlain _ -> False; SelectGroup _ -> False; _ -> True}
isCommonQuery (F _ b) = case b of {SelectGroup _ -> False; _ -> True}
isPlainQuery  (F _ b) = case b of {SelectPlain _ -> True;  _ -> False}
isMinMaxQuery (F _ b) = case b of {SelectMin _ -> True; SelectMax _ -> True; _ -> False}

-- substitute expressions of fs into aexpr
mergeQueryFuns :: [Function] -> AExpr VarName -> AExpr VarName
mergeQueryFuns fs aexpr =
    let aexprMap = M.fromList $ map (\(F aexpr2 b) ->
                                          case b of
                                              SelectPlain x -> (x,aexpr2)
                                              SelectGroup x -> let x = getVarNameFromTableExpr b in
                                                   let table = queryNameToTableName x in
                                                   let var   = queryNameToAggrName x in
                                                   (connectedVarName table var, ASubExpr table var False)
                                              _ -> let x = getVarNameFromTableExpr b in
                                                   let table = queryNameToTableName x in
                                                   let var   = queryNameToAggrName x in
                                                   (connectedVarName table var, ASubExpr table var True)
                                ) fs in
    aexprSubstitute aexprMap aexpr

-- adjust the query norm to the db norm (w.r.t. the given input table)
adjustQueryNormToDbNorm :: Bool -> Double -> (M.Map VarName B.Var) -> S.Set B.Var -> TableAlias -> NormFunction -> B.Expr -> B.TableExpr -> B.TableExpr
adjustQueryNormToDbNorm debug sigmoidPrecision inputMap sensitiveCols tableAlias tableNormFun queryExpr queryAggr =

    let namePrefix = if tableAlias == "" then tableAlias else tableAlias ++ [tsep] in
    let (dbNorm', dbAggrNorm) = normToExpr namePrefix (inputMap !) tableNormFun in
    let dbNorm = markNormCols sensitiveCols dbNorm' in

    let orderedVars = [0..M.size inputMap - 1] in
    let queryExprNorm = deriveNorm orderedVars queryExpr in
    let queryAggrNorm = deriveTableNorm queryAggr in

    -- we use inverse input map to make norm-related error messages readable
    let invInputMap = M.fromList $ map (\(x,y) -> (y,queryNameToVarName x)) (M.toList inputMap) in

    -- find the necessary norm scaling to match the query norm and the table norm
    let (mapCol,mapLN,mapLZ) = normalizeAndVerify invInputMap queryExprNorm dbNorm in

    -- apply scaling to the query
    let adjustedQuery = updateTableExpr sigmoidPrecision queryAggr mapCol mapLN mapLZ queryAggrNorm dbAggrNorm in

    -- these are needed only for debugging
    let newQueryNorm = deriveNorm orderedVars $ head (getExprFromTableExpr adjustedQuery) in
    let newAggrNorm  = deriveTableNorm adjustedQuery in

    traceIfDebug debug ("----------------") $
    traceIfDebug debug ("database norm     = Rows: " ++ show dbAggrNorm    ++ " | Cols: "  ++ show (normalizeNorm dbNorm)) $
    traceIfDebug debug ("intial query norm = Rows: " ++ show queryAggrNorm ++ " | Cols: "  ++ show (normalizeNorm queryExprNorm)) $
    traceIfDebug debug ("adjust query norm = Rows: " ++ show newAggrNorm   ++ " | Cols: "  ++ show (normalizeNorm newQueryNorm)) $
    traceIfDebug debug ("scaling: floats -- " ++ show mapCol ++ "\n\t float ln -- " ++ show mapLN ++ "\n\t discrete -- " ++ show mapLZ ++ "\n\n") $
    traceIfDebug debug ("----------------") $
    adjustedQuery

-- compute data for Banach analysis w.r.t. one set of sensitive variables, i.e. one input table or one intermediate table
dataWrtOneSensVarSet :: Bool -> Double -> (M.Map VarName B.Var) -> TableName -> TableAlias -> TableAlias ->
                        B.TableExpr -> (String,String,String) -> String ->
                        NormFunction -> (S.Set B.Var)
                        -> (BQ.AnalysisDataWrtTable, NormFunction)
dataWrtOneSensVarSet debug sigmoidPrecision inputMap tableName tableAlias tablePrefix filtQuery (sel,fr,wh) queryName tableNormFun tableSensCols =

    -- transform the main query to a banach expression; it is fine to use only the current table's sensitive columns
    let (queryExpr,  queryAggr)  = insertZeroSens tableSensCols filtQuery in

    -- the query will also take into account sensitive rows of the current sensitive table
    let sensRowTable  = tableName ++ "_sensRows" in
    let sensRowFilter = tableName ++ "_sensRows.ID = " ++ tableAlias ++ ".ID" in

    -- the large cross product table now includes the bit denoting whether the row is sensitive
    let fr1  = fr ++ ", " ++ sensRowTable in
    let wh1  = wh ++ " AND " ++ sensRowFilter in

    -- the query expressions defined over the large cross product table
    let adjTableExpr = adjustQueryNormToDbNorm debug sigmoidPrecision inputMap tableSensCols tablePrefix tableNormFun queryExpr queryAggr in
    (BQ.ADWT tableName queryName adjTableExpr (sel, fr1, wh1), tableNormFun)


-- compute data for Banach analysis w.r.t. some intermediate aggregation, whose output we treat as a sensitive variable
dataWrtIntermTable :: Bool -> Double -> (M.Map VarName B.Var) ->
                      B.TableExpr -> (String,String,String) -> String ->
                      VarName -> B.Var
                      -> (BQ.AnalysisDataWrtTable, NormFunction)
dataWrtIntermTable debug sigmoidPrecision inputMap filtQuery (sel,fr,wh) queryName intermediateSensVar intermediateSensCol =

    -- we treat the column that is an output of some aggregation as sensitive
    let inputTableName = varNameToTableName intermediateSensVar in
    let intermediateSensCols = S.singleton intermediateSensCol in
    let tableNormFun = NF (M.fromList [(defaultNormVariable ++ intermediateSensVar, Id intermediateSensVar)]) $ SelectMax (defaultNormVariable ++ intermediateSensVar) in
    dataWrtOneSensVarSet debug sigmoidPrecision inputMap inputTableName inputTableName "" filtQuery (sel,fr,wh) queryName tableNormFun intermediateSensCols

-- construct input for multitable Banach analyser
-- we read the columns in the order they are given in allTableNorms, since it matches the cross product table itself
dataWrtOneInputTable :: Bool -> Double -> (M.Map VarName B.Var) ->
                        B.TableExpr -> (String,String,String) -> String -> (M.Map TableAlias TableData) -> TableAlias
                        -> (BQ.AnalysisDataWrtTable, NormFunction)
dataWrtOneInputTable debug sigmoidPrecision inputMap filtQuery (sel,fr,wh) queryName tableMap tableAlias =

    let tableData     = tableMap ! tableAlias in
    let tableNormFun  = getNorm          tableData in
    let tableName     = getTableName     tableData in
    let tableSensVars = getSensCols      tableData in
    let tableSensCols = S.fromList $ map (inputMap ! ) tableSensVars in
    dataWrtOneSensVarSet debug sigmoidPrecision inputMap tableName tableAlias tableAlias filtQuery (sel,fr,wh) queryName tableNormFun tableSensCols

-- extract Gs of the tables (combined sensitivity only)
getTableGs tableMap =
    let tableAliases = M.keys tableMap in
    let tableGsMap   = M.fromList (map (\tableAlias -> let tableData = tableMap ! tableAlias in (getTableName tableData, getGG tableData)) tableAliases) in
    M.toList tableGsMap

-- generate dependencies between queries and input tables
processQuery :: TableName -> (M.Map TableName Query) -> AttMap -> 
                TableName -> TableAlias -> TableName
                -> ([[[String]]], [[TableAlias]],[[TableName]], [(TableAlias,TableName)], [GroupData], [(Function,String)], [[AExpr VarName]])
processQuery outputTableName queryMap attMap taskName tableAlias tableName =

    -- if the table is not in the query map, then it is an input table
    -- define the list of tasks [taskName] that depend on the pair (tableAlias,tableName)
    if not (M.member tableName queryMap) then
        if taskName == "" then error $ error_internal_empty_taskname tableName
        else ([[[taskName]]], [[tableAlias]], [[tableName]], [], [NoGR], [(F (AVar tableName) (SelectPlain tableName), tableName)], [[]])
    else
        -- collect all used tables of this query
        let query@(P groupVarNames queryFuns' usedAliasMap filterFuns') = queryMap ! tableName in

        -- we assume that the groups of 'group by' are followed by a single aggregation
        let ng = length groupVarNames in
        if ng > 0 && length queryFuns' /= ng + 1 then error $ error_queryExpr_groupBy else
        let (queryFuns,queryGroups,filterFuns) = if ng > 0 then

                                     -- use attMap and generate as many queries as there are groups
                                     let groupColNames = map (\(F as b) -> getVarNameFromTableExpr b) (init queryFuns') in
                                     let groupVarValues = map (getStateValues attMap) groupVarNames in
                                     let qs = map (\(F as b) -> F as (let x = getVarNameFromTableExpr b in SelectGroup x)) (init queryFuns') in
                                     let q  = (last queryFuns') in
                                     if isPlainQuery q then error $ error_queryExpr_groupBy else
                                     let gr' = GR "" groupColNames groupVarNames groupVarValues in
                                     let gr = if isMinMaxQuery q then trace warning_minMaxSubQueries gr' else gr' in
                                     let fs = filterFuns' in
                                     (q : qs, replicate (ng + 1) gr, replicate (ng + 1) fs)
                                 else
                                     (queryFuns', replicate (length queryFuns') NoGR, replicate (length queryFuns') filterFuns')
        in

        -- recursively, collect all subqueries and filters used to generate all used tables
        let usedAliases = M.keys usedAliasMap in
        let usedNames   = M.elems usedAliasMap in
        let subData = map (\key -> processQuery outputTableName queryMap attMap tableName key (usedAliasMap ! key)) usedAliases in
        let (usedTaskNames', tableAliases', tableNames', tableAliasesNamesSub', subQueryGroups',subQueryFuns', subFiltFuns') = unzip7 subData in

        let usedTaskNames  = concat usedTaskNames'  in
        let tableAliases   = concat tableAliases'   in
        let tableNames     = concat tableNames'     in
        let tableAliasesNamesSub   = concat tableAliasesNamesSub'   in
        let subQueryGroups = concat subQueryGroups' in
        let (subQueryFuns,subTaskNames) = unzip $ concat subQueryFuns' in
        let subFiltFuns    = concat subFiltFuns'    in

        -- add the current table alias as a prefix to all variables in all queries and filters
        let prefix             = if tableAlias == outputTableName then "" else tableAlias ++ [csep] in
        let prefixNoSubscript  = if tableAlias == outputTableName then "" else tableAlias in
        let fullTablePaths = S.fromList (concat tableAliases) in

        let newQueryFuns   = map (updateQueryVariableNames fullTablePaths prefix) queryFuns in
        let newFilterFuns  = map (map (updateAExprVariableNames fullTablePaths prefix)) filterFuns in
        let newQueryGroups = map ((\g -> if getGroupTableName g == "" then addPrefixToGroupTable prefixNoSubscript g else addPrefixToGroupTable prefix g) . addPrefixToGroupVar prefix) queryGroups in

        let newSubQueryGroups = map ((\g -> if getGroupTableName g == "" then addPrefixToGroupTable prefixNoSubscript g else addPrefixToGroupTable prefix g) . addPrefixToGroupVar prefix) subQueryGroups in
        let newSubQueryFuns = map (updateQueryVariableNames fullTablePaths prefix) subQueryFuns in
        let newSubFiltFuns  = map (\fs -> map (updateAExprVariableNames fullTablePaths prefix) fs) subFiltFuns in

        let preficedTableAliases =  map (map (prefix ++)) tableAliases in
        -- add taskName as the user of inputs if it is not ""
        let preficedTaskNames    =  if taskName == "" then usedTaskNames else map (map (taskName :)) usedTaskNames in

        -- all tables used by plain subqueries will be extracted
        -- put all subquery funs and all filters together with the current query's funs and filters
        let tuple = zip7 newSubQueryFuns newSubQueryGroups subTaskNames newSubFiltFuns preficedTableAliases tableNames preficedTaskNames in

        let (aggrSubQueryFuns,  aggrSubQueryGroups,  aggrTaskNames, aggrSubFiltFuns,  aggrSubTableAliases,  aggrSubTableNames, aggrUsedTaskNames) = unzip7 $ filter aggrQueryType tuple in
        let (               _,                   _,              _, plainSubFiltFuns, plainSubTableAliases, plainSubTableNames, plainUsedTaskNames) = unzip7 $ filter (not . aggrQueryType) tuple in

        -- the filters and tableAliases of this query block are recorded for each query of the block
        let n = length newQueryFuns in
        let outputQueryFuns = (map (\ (F qaexpr b) -> F (mergeQueryFuns newSubQueryFuns qaexpr) b) newQueryFuns) ++ aggrSubQueryFuns in
        let outputTaskNames = (replicate n tableName) ++ aggrTaskNames in

        let outputAliases    = (replicate n (concat plainSubTableAliases))   ++ aggrSubTableAliases in
        let outputNames      = (replicate n (concat plainSubTableNames))     ++ aggrSubTableNames in
        let outputUsedTaskNames  = (replicate n (concat plainUsedTaskNames)) ++ aggrUsedTaskNames in

        let outputGroupNames = newQueryGroups ++ aggrSubQueryGroups in
        let outputFilters    = (map (\x -> map (mergeQueryFuns newSubQueryFuns) x ++ concat plainSubFiltFuns) newFilterFuns) ++ aggrSubFiltFuns in

        (outputUsedTaskNames, outputAliases, outputNames, (tableAlias,tableName) : map (\(x,y) -> (prefix ++ x, y)) tableAliasesNamesSub, outputGroupNames, zip outputQueryFuns outputTaskNames, outputFilters)
        where aggrQueryType ((F _ b),_,_,_,_,_,_) = case b of {SelectPlain _ -> False; _ -> True}

-- construct table data
-- assume that the db norm files are located in 'dataPath'
readTableData :: Bool -> String -> AttMap -> PlcCostType->
                 M.Map TableName (M.Map String String) -> [TableName] -> [TableAlias]
                 -> IO (M.Map TableAlias TableData)
readTableData policy dataPath attMap plcMaps typeMap tableNames tableAliases = do

    -- collect all norm-related table data
    -- read table sensitivities from corresponding files
    -- mapM is a standard function [IO a] -> IO [a]
    let dbNormData = if policy then
            return (constructNormData tableNames attMap (getStatement plcMaps))
        else
            mapM (\tableName -> parseNormFromFile (typeMap ! tableName) $ dataPath ++ tableName ++ ".nrm") tableNames

    let badNames = filter (\t -> not (M.member t typeMap)) tableNames
    when (length badNames > 0) $ error (error_schema (M.keys typeMap) badNames)
    let tableColNames = map (\t -> M.keys (typeMap ! t)) tableNames

    (tableSensitives, tableNormFuns, tableGs) <- fmap unzip3 dbNormData
    let (tableSensRows,tableSensitiveVars) = unzip tableSensitives

    -- we put table names in front of column names
    let namePrefices = map (\tableAlias -> tableAlias ++ [tsep]) tableAliases
    let fullTableColNames = zipWith (\x ys -> map (\y -> x ++ y) ys) namePrefices tableColNames
    let fullSensitiveVarNames = zipWith (\x ys -> map (\y -> x ++ y) ys) namePrefices tableSensitiveVars

    -- put all table data together
    let tableData = zipWith6 T tableNames fullTableColNames fullSensitiveVarNames tableGs tableNormFuns tableSensRows
    let tableMap  = M.fromList $ zip tableAliases tableData
    return tableMap

-- for each column, find the number of times the table of this column is used
getColTableCounts colNames tableNames tableAliases =
    let
      -- the number of times each table is used
      tableCounts = map (\ tn -> length (filter (== tn) tableNames)) tableNames
      aliasToCountMap = M.fromList (zip tableAliases tableCounts)
      -- the table (alias) of each column
      colTableAliases = map varNameToTableName colNames
    in
      -- some column names come from intermediate queries
      -- we do not use colTableCounts for these extra variables
      -- we only need to insert some arbitrary value to maintain proper indexation
      map (\x -> if M.member x aliasToCountMap then aliasToCountMap M.! x else 1) colTableAliases


-- given a list of sublists, find all combinations of different sublist elements
allCombsOfLists [] = [[]]
allCombsOfLists (xs:xss) =
    [(y:ys) | y <- xs, ys <- allCombsOfLists xss]

cleanTypeName x =
    case x of
        "int"    -> "int"
        "bigint" -> "int"
        "bool"   -> "bool"
        "text"   -> "text"
        "float"  -> "float"
        "date"   -> "date"
        _        -> error $ error_typeDoesNotExist x

-- putting everything together
getBanachAnalyserInput :: ProgramOptions -> String -> String -> String -> String
                          -> IO (String,PlcCostType, AttMap, String, String, [String], Int, [String], [(String,[(String,String)])], BQ.TaskMap, [String], [BQ.DataWrtTable],[(String, Maybe Double)],[Int],[String],[String])
getBanachAnalyserInput args inputSchema inputQuery inputAttacker inputPolicy = do

    let debug = not (alternative args) && not (succinct args)
    let policy = policyAnalysis args

    -- used for generating benchmarks
    --putStrLn $ "\\echo ##" ++ inputQuery

    let dataPath = reverse $ dropWhile (/= '/') (reverse inputSchema)

    queryFileContents <- readInput inputQuery
    (outputTableName,queryMap) <- parseQueryMap defaultOutputTableName queryFileContents
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Query map: " ++ show queryMap
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "Output table name: " ++ show outputTableName

    schemaFileContents <- readInput inputSchema
    schemas <- parseSchemas schemaFileContents

    let typeList' = map extractTypes schemas
    let typeList  = map (\(x,ys) -> (x, map (\(y1,y2) -> (y1, (cleanTypeName . takeWhile (\z -> ord(z) >= 65)) (map toLower y2) )) ys)) typeList'
    let typeMap  = M.fromList $ map (\(x,ys) -> (x, M.fromList ys)) typeList

    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "Type map: " ++ show typeMap

    let plainTypeMaps = map (\(tname,tmap) -> map (\(x,y) -> (preficedVarName tname x,y)) tmap) typeList
    let plainTypeMap  = M.fromList $ concat plainTypeMaps

    plcMaps <- parsePolicyFromFile inputPolicy
    attMap' <- parseAttackerFromFile inputAttacker

    -- verify that the types of attMap and the schema match
    let attMap = update_varStates attMap' plainTypeMap

    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "Att map: " ++ show attMap
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "Plc map: " ++ show plcMaps

    -- verify that all columns in the attMap do exist (to prevent attacker knowledge loss due to typos)
    let badAttMapVars = foldr (\x ys -> if  M.member x plainTypeMap then ys else (x : ys)) [] $ M.keys attMap
    when (length badAttMapVars > 0) $ traceIO (warning_badAttackerVars badAttMapVars)

    -- extract the tables that should be read from input files, take into account copies
    -- substitute intermediate queries into the aggregated query
    let (usedTaskNames', inputTableAliases', inputTableNames', subTableAliasMap, subexprGroups, subexprQueryFuns', filterAexprs') = processQuery outputTableName queryMap attMap "" outputTableName outputTableName
    let (subexprQueryFuns, taskNames) = unzip subexprQueryFuns'

    -- by construction, the used table aliases may repeat, so we discard repetitions first
    let (inputTableAliases, inputTableNames, usedTaskNames) = unzip3 $ zipWith3 (\xs ys zs -> unzip3 $ S.toList $ S.fromList $ zip3 xs ys zs) inputTableAliases' inputTableNames' usedTaskNames'
    let (allInputTableNames,allInputTableAliases) = unzip $ nub $ zip (concat inputTableNames) (concat inputTableAliases)
    let tableAliasMap = M.union (M.fromList $ map (\(x,y) -> (y,[x])) subTableAliasMap) $ M.fromListWith (++) $ zip allInputTableNames (map (\x -> [x]) allInputTableAliases)

    let (outputQueryFuns,intermediateQueryFuns) = (\(xs,ys) -> (map fst xs, map fst ys)) $ partition (\(qf,tn) -> tn == outputTableName) $ zip subexprQueryFuns taskNames
    let (outputGroups,   intermediateGroups)    = (\(xs,ys) -> (map fst xs, map fst ys)) $ partition (\(qf,tn) -> tn == outputTableName) $ zip subexprGroups taskNames

    let commonOutputQueryFuns = filter isCommonQuery outputQueryFuns
    --when (length commonOutputQueryFuns > 1) $ error error_queryExpr_singleColumn

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "All (sub)queries: " ++ show subexprQueryFuns
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "All task names: " ++ show taskNames
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "All groups: " ++ show subexprGroups
    traceIOIfDebug debug $ "***"
    traceIOIfDebug debug $ "Output (sub)queries: " ++ show outputQueryFuns
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "Output groups: " ++ show outputGroups
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "Intermediate (sub)queries: " ++ show intermediateQueryFuns
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "intermediate groups: " ++ show intermediateGroups
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Used task names: " ++ show usedTaskNames
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "Input table names: " ++ show inputTableNames'
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "Input table aliases: " ++ show inputTableAliases'
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Input table name set: " ++ show allInputTableNames
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "Input table alias set: " ++ show allInputTableAliases
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "Subtable aliases: " ++ show subTableAliasMap
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "Table alias map: " ++ show tableAliasMap

    -- create a map that is analogous to attMap, but is defined on tableAliases instead of tableNames
    let fullAttMap  = M.fromList $ concat $ map (\(varName,varState) ->
                                                    let [tableName,x] = varNameToTableAndSubVarName varName in
                                                    let xs = if M.member tableName tableAliasMap then (tableAliasMap ! tableName) else [] in
                                                    map (\ta -> (preficedVarName ta x, varState)) xs
                                                ) (M.toList attMap)

    -- inputTableMap maps input table aliases to the actual table data that it reads from file (table contents, column names, norm, sensitivities)
    inputTableMap <- readTableData policy dataPath attMap plcMaps typeMap allInputTableNames allInputTableAliases
    let plcFilterMap = if policy then M.fromList $ getFilters plcMaps else M.empty

    -- the columns of the cross product are ordered according to "M.keys inputTableMap"
    let orderedTableAliases = M.keys inputTableMap

    let subExprsQ = map (\ (F aexpr _) -> getAllSubExprs False aexpr) subexprQueryFuns
    let subExprsF = map (\fs -> foldr S.union S.empty (map (getAllSubExprs False) fs)) filterAexprs'
    let subExprs  = zipWith S.union subExprsQ subExprsF

    let intermediateColNameSetsQ = map (S.map fst) subExprsQ
    let intermediateColNameSetsF = map (S.map fst) subExprsF
    let intermediateColNameSets = intermediateColNameSetsQ ++ intermediateColNameSetsF

    let allIntermediateGroupColNameList = concat $ map (\gr -> let (x,ys) = (getGroupTableName gr, getGroupColName gr) in map (preficedVarName x) ys) subexprGroups
    let allIntermediateColNameList      = map (uncurry preficedVarName) $ concat $ map S.toList intermediateColNameSets

    let uniqueSubExprvarList = S.toList $ S.fromList $ allIntermediateColNameList ++ allIntermediateGroupColNameList

    -- check whether the output of the same subquery is used in several other subqueries
    -- we do not count group equality checks, as the set of possible groups should be public anyway
    -- we discover the cases where t.x1 and t.x2 for x1 /= x2 are used in the same query (unless one of them is public or is a group)
    -- we discover the cases where t.x is used by different queries (unless it is a group)
    -- using t.x multiple times in the same query is safe, since it is treated as the same variable
    let subExprTables = concat $ map (map (fst . fst) . filter (\(_,b) -> b) . S.toList) subExprs

    --let subExprTables  = zipWith (++) subExprTablesQ subExprTablesF
    --let goodQueries    = map (\xs -> length xs == S.size (S.fromList xs)) subExprTables
    --when (foldr (&&) True goodQueries == False) $ error $ error_subQueries
    let goodQueries    = length subExprTables == S.size (S.fromList subExprTables)
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "subExprsQ: " ++ show subExprsQ
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "subExprsF: " ++ show subExprsF
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "subExprs: " ++ show subExprs
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "subExprTables: " ++ show subExprTables
    when (goodQueries == False) $ error $ error_subQueries

    let inputColNames    = concat $ map (getUsedCols . (inputTableMap ! ) ) orderedTableAliases
    let colNames         = inputColNames ++ uniqueSubExprvarList
    let sensitiveVarList = concat $ map (getSensCols . (inputTableMap ! ) ) orderedTableAliases

    let (subTableNames, subTableAliases) = unzip $ nub $ subTableAliasMap
    let fullTypeMap1 = foldr M.union M.empty $ zipWith (\tableAlias tableName -> M.mapKeys (preficedVarName tableAlias) (typeMap ! tableName)) allInputTableAliases allInputTableNames
    let fullTypeMap2 = foldr M.union M.empty $ map (\(tableAlias,tableName) -> if M.member tableName typeMap then M.mapKeys (preficedVarName tableAlias) (typeMap ! tableName) else M.empty) subTableAliasMap
    let fullTypeMap3 = foldr M.union M.empty $ zipWith (\tableAlias tableName -> if M.member tableName typeMap then M.mapKeys (preficedVarName tableAlias) (typeMap ! tableName) else M.empty) subTableAliases subTableNames
    let fullTypeMap = M.union (M.union fullTypeMap1 fullTypeMap2) fullTypeMap3

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Intermediate Vars: " ++ show allIntermediateColNameList
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "Group Vars: " ++ show allIntermediateGroupColNameList
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Types plain: " ++ show typeMap
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "Types preficed: " ++ show fullTypeMap
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Att plain: " ++ show attMap
    traceIOIfDebug debug $ "*"
    traceIOIfDebug debug $ "Att preficed: " ++ show fullAttMap

    -- assign a unique integer to each column name, which is the order of this column in the cross product table
    let inputMap        = M.fromList $ zip colNames [0..length colNames - 1]
    let sensitiveColSet = S.fromList $ map (\x -> if M.member x inputMap then
                                                      inputMap ! x
                                                  else
                                                      error $ error_badNormVariable policy (queryNameToVarName x) (map queryNameToVarName $ M.keys inputMap)
                                           ) sensitiveVarList

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "All input variables: " ++ show inputMap
    traceIOIfDebug debug $ "All sensitive vars:  " ++ show sensitiveVarList
    traceIOIfDebug debug $ "All sensitive cols:  " ++ show sensitiveColSet

    let filterAexprs = map (map (snd . applyAexprTypes fullTypeMap)) filterAexprs'

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "All query funs (w/o filter): " ++ show subexprQueryFuns
    traceIOIfDebug debug $ "Used input table names: " ++ show inputTableNames
    traceIOIfDebug debug $ "Used input table aliases: " ++ show inputTableAliases
    traceIOIfDebug debug $ "All filters:" ++ show filterAexprs


    -- process the query blocks one by one, concatenate and reverse, so that subqueries would be processed before superqueries
    let initialSubQueryDataMap = M.fromList $ zipWith6 (\t g q f ts tn -> let qn = getQueryName q in (qn,(t,g,q,f,ts,tn))) inputTableAliases subexprGroups subexprQueryFuns filterAexprs usedTaskNames taskNames
    let orderedQueryNames = map getQueryName subexprQueryFuns
    let subQueryDataMap'  = constructQueryData initialSubQueryDataMap orderedQueryNames

    -- remove the auxiliary group-tables, as we do not need them anymore
    let commonOrderedQueryNames = filter ((\(_,_,_,_,_,_,q,_,_,_) -> isCommonQuery q) . (subQueryDataMap' M.!)) orderedQueryNames
    let subQueryDataMap         = M.filter (\(_,_,_,_,_,_,q,_,_,_) -> isCommonQuery q) $ foldl (\x y -> removeGroupFromSubQueryMap commonOrderedQueryNames x y) subQueryDataMap' orderedQueryNames
    let outputQueryName = last commonOrderedQueryNames

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "commonOrderedQueryNames: " ++ show commonOrderedQueryNames
    traceIOIfDebug debug $ "Subquery Map: " ++ show subQueryDataMap
    traceIOIfDebug debug $ "----------------"

    -- reconstruct the initial query
    let allQueryStrs = M.fromList $ map (\f -> let qn = getQueryName f in (qn, constructInitialQuery subQueryDataMap' inputTableMap qn)) subexprQueryFuns
    let initialQuery = allQueryStrs ! (getQueryName $ head subexprQueryFuns)
    let initialQueryGroups = ((\(_,_,_,_,_,gr,_,_,_,_) -> gr) (subQueryDataMap ! outputQueryName))
    let numOfOutputs = product $ map length (getGroupValues initialQueryGroups)

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Initial query: " ++ initialQuery
    traceIOIfDebug debug $ "Initial query groups: " ++ show initialQueryGroups
    traceIOIfDebug debug $ "number of outputs: " ++ show numOfOutputs
    traceIOIfDebug debug $ "----------------"

    let dataWrtEachTable = concat $ map (getQueryData debug policy (getSigmoidBeta args) (getSigmoidPrecision args) fullAttMap inputMap inputTableMap plcFilterMap (M.fromList subTableAliasMap) fullTypeMap subQueryDataMap sensitiveVarList allQueryStrs) (reverse commonOrderedQueryNames)

    let (tableNameList,_,_) = unzip3 $ map BQ.getExtra dataWrtEachTable
    let taskMap = BQ.TM $ nub $ map (\t -> if t == outputTableName then (t,True) else (t,False)) tableNameList

    -- additional parameters
    let tableGs = getTableGs inputTableMap
    let colTableCounts = getColTableCounts colNames allInputTableNames allInputTableAliases

    -- if we are using combined sensitivity, then groups are not allowed
    --let usingCombinedSensitivity = foldr (||) False $ map (\g -> case g of {Just a -> if a == 1/0 then False else True; _ -> True}) (map snd tableGs)
    --when (usingCombinedSensitivity && length subexprQueryFuns > 1) $ error $ error_noCSGroupSupport
    when (combinedSens args && length subexprQueryFuns > 1) $ error $ error_noCSGroupSupport

    -- the last column now always marks sensitive rows
    let extColNames = colNames ++ ["sensitive"]

    -- TODO is it a proper place for table Gs if groups are used? we decide it when extend the groups to combined sensitivity
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Task Map: " ++ show taskMap
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Table Names:" ++ show allInputTableNames
    traceIOIfDebug debug $ "Table Aliases:" ++ show allInputTableAliases
    traceIOIfDebug debug $ "Table Gs: " ++ show tableGs
    traceIOIfDebug debug $ "colTableCounts: " ++ show colTableCounts
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "----------------"
    --traceIOIfDebug debug $ "tableExprData:" ++ show tableExprData
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "column names: " ++ show extColNames
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "----------------"


    -- generate the tables for intermediate aggragate queries
    -- let aggrIntermediateQueryFuns = filter (\(x,_) -> isAggrQuery x) $ zip (tail subexprQueryFuns) (tail subexprGroups)
    let aggrIntermediateQueryFuns = filter (\(x,_) -> isAggrQuery x) $ zip intermediateQueryFuns intermediateGroups

    -- the follwing queries are called as a part of performAnalyses, to avoid duplications during beta optimization
    when debug $ putStrLn "================================="
    when debug $ putStrLn "Generating SQL statements for creating empty intermediate query tables:\n"
    let subtableQueries = concat $ map (\ ((F _ y),z) -> let x = getVarNameFromTableExpr y in initIntermediateAggrTableSql fullTypeMap x z) aggrIntermediateQueryFuns
    traceIOIfDebug debug $ "Subtable queries : " ++ show subtableQueries


    let uniqueTableNamesAndSR = M.toList $ M.fromList $ M.elems $ M.map (\td -> (getTableName td, getSensRows td)) inputTableMap
    let separator = delimiter args
    when debug $ putStrLn "Generating SQL statements for creating input tables:\n"
    ctss <- if (not (dbCreateTables args)) then (do return []) else
              forM uniqueTableNamesAndSR $ \ (t,sR) -> do
                                                         cts <- createTableSqlTyped args dataPath separator t sR typeList
                                                         when debug $ putStr (concatMap (++ ";\n") cts)
                                                         return cts

    let initQueries = subtableQueries ++ if dbCreateTables args then concat ctss else []
    sendQueriesToDbAndCommit args initQueries

    -- return data to the banach space analyser
    let tableExprData = (outputTableName,plcMaps,attMap,dataPath,initialQuery,initQueries,numOfOutputs, extColNames, typeList, taskMap, sensitiveVarList, dataWrtEachTable, tableGs,
                         colTableCounts, allInputTableNames, allInputTableAliases)
    return tableExprData

removeGroupFromSubQueryMap :: [String] -> M.Map String ([TableAlias],[TableAlias],[TableAlias],[Bool],[VarName],GroupData,Function, [AExpr VarName], [[String]], String) -> String
                              -> M.Map String ([TableAlias],[TableAlias],[TableAlias],[Bool],[VarName],GroupData,Function, [AExpr VarName], [[String]], String)
removeGroupFromSubQueryMap qs subQueryDataMap queryName =
    let (directTableAliases,subqueryTableAliases',intermediateVarList,intermediateIsGrList,directColNames,groups,query,filterAexprs,usedTaskNames,taskName) = subQueryDataMap ! queryName in
    let subqueryTableAliases = filter (\x -> elem x qs) subqueryTableAliases' in
    M.insert queryName (directTableAliases,subqueryTableAliases,intermediateVarList,intermediateIsGrList,directColNames,groups,query,filterAexprs,usedTaskNames,taskName) subQueryDataMap

-- we are dealing with a particular task name that is 
constructQueryData :: M.Map String ([TableAlias],GroupData, Function, [AExpr VarName], [[String]], String) -> [String] ->
                      M.Map String ([TableAlias],[TableAlias],[TableAlias],[Bool],[VarName],GroupData,Function, [AExpr VarName], [[String]], String)
constructQueryData _ [] = M.empty
constructQueryData initialSubQueryDataMap (queryName:qs) =

    -- first of all, collect all table aliases used by all subqueries
    let subQueryDataMap = constructQueryData initialSubQueryDataMap qs in

    -- process the current query
    let (directTableAliases,groups,query,filterAexprs,usedTaskNames,taskName) = initialSubQueryDataMap ! queryName in

    -- if some subtable is used multiple times, we still record it only once
    let directColNamesQ = (\ (F aexpr _) -> getAllAExprVars False aexpr) query in
    let directColNamesF = foldr S.union S.empty $ map (getAllAExprVars False) filterAexprs in
    let directColNames = S.toList $ S.union directColNamesQ directColNamesF in

    -- all direct column names need to be preficed, since our analyser does not check which columns come from which table
    let goodVars = map (\x -> if elem tsep x then True else False) directColNames in
    if not (foldr (&&) True goodVars) then error $ error_queryExpr_prefices directColNames else

    let subExprsQ = (\ (F aexpr _) -> getAllSubExprs False aexpr) query in
    let subExprsF = foldr S.union S.empty $ map (getAllSubExprs False) filterAexprs in

    let intermediateVarGroupListQ = S.map (\ ((x,y),b) -> (preficedVarName x y, b)) subExprsQ in
    let intermediateVarGroupListF = S.map (\ ((x,y),b) -> (preficedVarName x y, b)) subExprsF in
    let intermediateVarGroupList  = S.toList $ S.union intermediateVarGroupListQ intermediateVarGroupListF in

    let (intermediateVarList, intermediateIsCommonList)  = unzip intermediateVarGroupList in

    -- collect all table aliases used by all subqueries
    let subqueryTableAliases = concat $ map (\x -> let (ts1,ts2,_,_,_,_,_,_,_,_) = subQueryDataMap ! (varNameToQueryName x) in ts1 ++ ts2) intermediateVarList in
    let entry = (directTableAliases,subqueryTableAliases,intermediateVarList,intermediateIsCommonList,directColNames,groups,query,filterAexprs,usedTaskNames,taskName) in

    -- add the new record to the map
    M.insert queryName entry subQueryDataMap

constructInitialQuery :: M.Map String ([TableAlias],[TableAlias],[TableAlias],[Bool],[VarName],GroupData, Function, [AExpr VarName],[[String]],String) -> (M.Map TableAlias TableData) -> String -> String
constructInitialQuery subQueryDataMap inputTableMap queryName =

    -- process the current query
    let (directTableAliases,_,intermediateVarList,intermediateIsCommonList,_,groups,query,filterAexprs,_,_) = subQueryDataMap ! queryName in

    let directTables        = map (\x -> let z = getTableName (inputTableMap ! x) in if x == z then z else z ++ " AS " ++ x) directTableAliases in
    let intermediateTables  = map varNameToTableName intermediateVarList in

    let queryStr  = queryAggrToString query in
    let filtersStr = map aexprToString filterAexprs in

    -- add groups
    let groupVar = if hasGroups groups then concat $ zipWith (\gv gc -> gv ++ " AS " ++ gc ++ ",") (getGroupVarName groups) (getGroupColName groups) else "" in
    let groupBy  = if hasGroups groups then " GROUP BY " ++ (intercalate ", " (getGroupVarName groups)) else "" in
    --let alias    = if isIntermediateQueryName queryName && isAggrQuery query then " AS " ++ (queryNameToVarName queryName) else "" in
    let alias    = if isAggrQuery query then " AS " ++ (queryNameToVarName queryName) else "" in
    let mainSelect = "SELECT " ++ groupVar ++ queryStr ++ alias in
    --let mainFrom   = intercalate ", " directTables in
    let mainWhere  = if length filtersStr == 0 then "true" else intercalate " AND " filtersStr in

    -- the groups themselves do not need to be processed, so discard them from the list of subtables
    let subIntermediateVarList = map snd $ filter (\(b,_) -> b) $ zip intermediateIsCommonList intermediateVarList in
    let subFroms = map (\x -> "(" ++ constructInitialQuery subQueryDataMap inputTableMap (varNameToQueryName x) ++ ") AS " ++ (varNameToTableName x)) subIntermediateVarList in

    -- add the subqueries to the FROM list
    (mainSelect ++ " FROM " ++ (intercalate ", " (directTables ++ subFroms)) ++ " WHERE " ++ mainWhere ++ groupBy)


getQueryData :: Bool -> Bool -> Double -> Double -> AttMap -> M.Map VarName B.Var -> M.Map TableAlias TableData -> M.Map TableName (AExpr VarName) -> M.Map TableName String -> M.Map TableName String ->
                M.Map String ([TableAlias],[TableAlias],[TableAlias],[Bool],[VarName], GroupData, Function, [AExpr VarName], [[String]], String) ->
                [VarName]-> M.Map String String ->
                String
                -> [BQ.DataWrtTable]
getQueryData debug policy sigmoidBeta sigmoidPrecision attMap inputMap inputTableMap plcFilterMap subTableAliasMap fullTypeMap queryDataMap globalSensitiveVarList allQueryStrs queryName =

    let (_,_,_,_,_,gr,_,_,_,_) = queryDataMap ! queryName in

    let groupColName = getGroupColName gr in
    let groupVarName = getGroupVarName gr in
    let groupList    = getGroupValues gr in

    concat $ map (getQueryDataForGroup debug policy sigmoidBeta sigmoidPrecision attMap inputMap inputTableMap plcFilterMap subTableAliasMap fullTypeMap queryDataMap globalSensitiveVarList queryName allQueryStrs groupVarName groupColName) (allCombsOfLists groupList)

getQueryDataForGroup :: Bool -> Bool -> Double -> Double -> AttMap -> M.Map VarName B.Var -> M.Map TableAlias TableData -> M.Map TableName (AExpr VarName) -> M.Map TableName String ->M.Map TableName String ->
                        M.Map String ([TableAlias],[TableAlias],[TableAlias],[Bool],[VarName], GroupData, Function, [AExpr VarName], [[String]], String) ->
                        [VarName] -> String -> M.Map String String -> [String] -> [String] ->
                        [Either Int String]
                        -> [BQ.DataWrtTable]
getQueryDataForGroup debug policy sigmoidBeta sigmoidPrecision attMap inputMap inputTableMap plcFilterMap subTableAliasMap fullTypeMap queryDataMap globalSensitiveVarList queryName allQueryStrs groupVarNames groupColNames groupValues =

    let (directTableAliases,subqueryTableAliases,intermediateVarList,intermediateIsCommonList,directColNames,gr,query,filterAexprs',usedTaskNames,taskName) = queryDataMap ! queryName in

    -- put the direct table aliases in place of corresponding table names in plcFilterMap
    let fullTablePaths = S.fromList directTableAliases in
    let filtStr = intercalate " AND " $ map (\ta -> let tn = getTableName (inputTableMap ! ta) in
                                                    let prefix = ta ++ [tsep] in
                                                    if M.member tn plcFilterMap then aexprToString $ updatePreficesAexpr fullTablePaths prefix (plcFilterMap ! tn) else "true"
                                            ) directTableAliases
    in

    -- each group creates a separate one-output query with a group filter
    let (filterAexprs, group, newQueryName) =

            let x1 = zipWith (\groupVarName groupValue -> 
                    let groupType = fullTypeMap ! groupVarName in
                    if  groupType == "int" || groupType == "float" then
                        let val = case groupValue of {Left c -> c; Right c -> error $ error_badGroupType groupVarName c groupType} in
                        ABinary AEQint (AVar groupVarName) (AConst $ fromIntegral val)
                    else
                        let val = case groupValue of {Right c -> c; Left c -> error $ error_badGroupType groupVarName (show c) groupType} in
                        ABinary AEQstr (AVar groupVarName) (AText val)
                    ) groupVarNames groupValues ++ filterAexprs'
            in
                let groupValuesAsStrings = map (\x -> case x of {Left y -> show y; Right y -> y}) groupValues in
                let x2 = OneGR groupColNames groupValuesAsStrings in
                let x3 = addGroupToQName queryName groupValuesAsStrings in
                (x1,x2,x3)
    in
    let queryStr   = queryToString query in
    let queryAExpr = queryToAExpr  query in

    -- TODO not all intermediate variables are necessarily sensitive, probably do not need to put all of them into the list
    let sensitiveVarListQ = S.toList $ (\ (F aexpr _) -> getAllAExprVars False aexpr) query in
    let sensitiveVarListF = concat $ map (S.toList . (getAllAExprVars False)) filterAexprs in
    let sensitiveVarList = (S.toList (S.intersection (S.fromList globalSensitiveVarList) (S.fromList (sensitiveVarListQ ++ sensitiveVarListF)))) ++ intermediateVarList in

    let sensitiveColList = map (inputMap ! ) sensitiveVarList in
    let sensitiveColSet  = S.fromList sensitiveColList in
    let sensitiveVarSet  = S.fromList (map queryNameToVarName sensitiveVarList) in


    let aexprAttMap = doubleRangesToAexprRanges attMap in
    let queryRange = aexprRange subTableAliasMap fullTypeMap aexprAttMap sensitiveVarSet queryAExpr in
    let queryRangeLB = getRangeLB queryRange in
    let queryRangeUB = getRangeUB queryRange in
    let queryRangeLBstr = aexprToString queryRangeLB in
    let queryRangeUBstr = aexprToString queryRangeUB in
    {-
    trace ("==================" ++ show queryStr) $
    trace ("==================" ++ show queryAExpr) $
    trace ("==================" ++ show queryRangeLB) $
    trace ("==================" ++ show queryRangeUB) $
    trace ("==================" ++ show queryRangeLBstr) $
    trace ("==================" ++ show queryRangeUBstr) $
    -}

    -- we filter out rows using _globally_ public filters, since different filterings would be bad for sensitivity over all tables
    let filterSensVars = map (\x -> S.intersection (S.fromList sensitiveVarList) (getAllAExprVars True x)) filterAexprs in
    let (filtQueryFun', pubFilterAexprs) = addFiltersToQuery query filterAexprs filterSensVars in

    let F queryAexpr' queryAggr' = filtQueryFun' in
    if ((case queryAggr' of {SelectAvg y -> True; _ -> False}) && (length filterSensVars > 1 || S.size (head filterSensVars) > 0)) then error error_queryExpr_aggrAvg else
    -- we divide each row output by COUNT(*) to get the average
    let filtQueryFun = (case queryAggr' of {SelectAvg y -> F (ABinary AMult queryAexpr' (AText "(countT.cntinv)")) (SelectSum y); _ -> filtQueryFun'}) in

    let (queryExpr,queryAggr,filtQueryStr) = queryToExpr sigmoidBeta inputMap sensitiveColSet (applyQueryTypes fullTypeMap filtQueryFun) in
    let pubFilter  = map aexprToString pubFilterAexprs in


    -- we remove the group-related intermediate varibles since we do not need them
    -- TODO take a set if we are sure that we can handle repeating variables
    let commonIntermediateVarList = map snd $ filter (\(b,_) -> b) $ zip intermediateIsCommonList intermediateVarList in
    let commonIntermediateColList = map (inputMap ! ) commonIntermediateVarList in

    traceIfDebug debug ("\n=== Processing subquery " ++ queryName ++ " ===") $
    {-
    traceIfDebug debug ("----------------") $
    traceIfDebug debug ("Query (w/o filter) = " ++ queryStr) $
    traceIfDebug debug ("Number of Filters: " ++ show (length filterAexprs)) $
    traceIfDebug debug ("Filters: " ++ show filterAexprs) $
    traceIfDebug debug ("Query intermediate vars: " ++ show intermediateVarList) $
    traceIfDebug debug ("Query groups: " ++ show gr) $
    traceIfDebug debug ("----------------") $
    traceIfDebug debug ("Query sensitive vars: " ++ show sensitiveVarList) $
    traceIfDebug debug ("Public filter: " ++ show pubFilter) $
    traceIfDebug debug ("Query with private filters: " ++ filtQueryStr) $
    traceIfDebug debug ("filterSensVars: " ++ show filterSensVars) $
    traceIfDebug debug ("directTableAliases: " ++ show directTableAliases) $
    traceIfDebug debug ("subqueryTableAliases: " ++ show subqueryTableAliases) $
    traceIfDebug debug ("commonIntermediateVarList: " ++ show commonIntermediateVarList) $
    traceIfDebug debug ("used task Names: " ++ show usedTaskNames) $
    -}

    -- a query that creates the large cross product table
    let directTables        = map (\x -> let z = getTableName (inputTableMap ! x) in if x == z then z else z ++ " AS " ++ x) directTableAliases in
    let intermediateTables  = map varNameToTableName intermediateVarList in
    let uniqueTables        = S.toList $ S.fromList $ directTables ++ intermediateTables in
    -- TODO rename variable 'sel' to avoid confusion, as this is not a select anymore
    --let sel = intercalate ", " directColNames in
    let sel = filtStr in
    let fr  = intercalate ", " uniqueTables in
    let wh  = if length pubFilter == 0 then "true" else intercalate " AND " pubFilter in

    -- compute min/max queries using sel, fr, wh
    -- TODO not optimal if the query in turn uses aggregate subqueries
    let additionalQuery = case queryAggr of
                          B.SelectMin  _ -> ", (SELECT MIN(" ++ queryRangeLBstr ++ ") AS min, MAX(" ++ queryRangeUBstr ++ ") AS max FROM " ++ fr ++ " WHERE " ++ wh ++ ") AS minmaxT"
                          B.SelectMax  _ -> ", (SELECT MIN(" ++ queryRangeLBstr ++ ") AS min, MAX(" ++ queryRangeUBstr ++ ") AS max FROM " ++ fr ++ " WHERE " ++ wh ++ ") AS minmaxT"
                          B.SelectSump _ _ -> ", (SELECT COUNT(*) AS cnt, 1.0 / COUNT(*) AS cntinv FROM " ++ fr ++ " WHERE " ++ wh ++ ") AS countT"
                          _                -> ""
    in
    let initQueryParts = (sel,fr ++ additionalQuery,wh) in

    -- construct tableExprData for both main query and all the subqueries
    let dataWrtEachTable' = map (dataWrtOneInputTable debug sigmoidPrecision inputMap queryAggr initQueryParts newQueryName inputTableMap) directTableAliases
           ++ zipWith (dataWrtIntermTable debug sigmoidPrecision inputMap queryAggr initQueryParts newQueryName) commonIntermediateVarList commonIntermediateColList in

    -- for each intermediate variable (a subquery), collect all tasks that depend on that subquery
    let internalUsedTaskNames = map (\cv -> let (_,_,_,_,_,_,_,_,usedTasks,_) = queryDataMap ! (varNameToQueryName cv) in concat usedTasks) commonIntermediateVarList in
    let allUsedTaskNames = usedTaskNames ++ internalUsedTaskNames in
    let (analysisData, normFuns) = unzip dataWrtEachTable' in

    -- construct a norm where variable names are used, not variable Id-s, these norms will be output to the user
    let idMap = M.fromList $ zip (M.keys inputMap) (M.keys inputMap) in
    let (normExprs,normAggrs) = unzip $ map (normToExpr "" id) normFuns in

    let groupList = replicate (length analysisData) group in
    let taskNames = replicate (length analysisData) taskName in
    let queryStrs = replicate (length analysisData) (allQueryStrs ! queryName) in

    let extra = zip3 taskNames normExprs normAggrs in
    let dataWrtEachTable = zipWith5 BQ.DWT analysisData groupList allUsedTaskNames queryStrs extra in

    {-
    traceIfDebug debug ("----------------") $
    traceIfDebug debug ("SELECT: " ++ show sel) $
    traceIfDebug debug ("----------------") $
    traceIfDebug debug ("FROM: " ++ show fr) $
    traceIfDebug debug ("----------------") $
    traceIfDebug debug ("WHERE: " ++ show wh) $
    traceIfDebug debug ("----------------") $
    -}

    dataWrtEachTable

