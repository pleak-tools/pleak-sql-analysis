module PreprocessQ where

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
import System.IO.Unsafe


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
isAggrQuery (F _ b) = case b of {SelectPlain _ -> False; SelectGroup _ -> False; _ -> True}
isCommonQuery (F _ b) = case b of {SelectGroup _ -> False; _ -> True}

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

-- this checks that the subqueries are all of select-type
--badQFuns :: [Function] -> (Bool, String)
--badQFuns [] = (False,"")
--badQFuns (F _ b : qs) =
--    case b of
--        SelectPlain _ -> badQFuns qs
--        _        -> (True, error_queryExpr_aggrInterm b)

deriveExprNorm :: Bool -> (M.Map VarName B.Var) -> S.Set B.Var -> [TableAlias] -> [NormFunction] -> B.Expr -> B.TableExpr -> B.TableExpr
deriveExprNorm debug inputMap sensitiveCols dbNormTableAliases dbNormFuns queryExpr queryAggr =

    let namePrefices = map (\tableAlias -> if tableAlias == "" then tableAlias else tableAlias ++ [tsep]) dbNormTableAliases in
    let (dbNorms1,dbAggrNorms) = unzip $ zipWith (\x y -> normToExpr x inputMap y) namePrefices dbNormFuns in
    let dbNorms = map (markNormCols sensitiveCols) dbNorms1 in

    -- if there are several tables, we assume that we compute sensitivity w.r.t. max of them
    -- since the same row can be used multiple times in the cross product, we need max here for the correctness of result w.r.t. all tables
    -- let dbExprNorm = NormL Any dbNorms in
    -- BanachQ will use linf-norm in the places where the same row repeats, and leaves dbAggrNorm in the other places
    let dbAggrNorm = foldr takeFiner (Exactly 1.0) dbAggrNorms in

    let orderedVars = [0..M.size inputMap - 1] in
    let queryExprNorm = deriveNorm orderedVars queryExpr in
    let queryAggrNorm = deriveTableNorm queryAggr in

    -- adjust the query to the database norm
    -- let (mapCol,mapLN,mapLZ) = normalizeAndVerify queryExprNorm dbExprNorm in
    -- since we compute w.r.t. each table separately anyway, it is sufficient to add the scalings for each table norm separately
    let (mapCol,mapLN,mapLZ) = foldr (\x (y1,y2,y3) -> let (z1,z2,z3) = normalizeAndVerify queryExprNorm x in (M.unionWith min y1 z1, M.unionWith min y2 z2, M.unionWith min y3 z3)) (M.empty,M.empty,M.empty) dbNorms in

    let adjustedQuery = updateTableExpr queryAggr mapCol mapLN mapLZ queryAggrNorm dbAggrNorm in

    let newQueryNorm = deriveNorm orderedVars $ head (getExprFromTableExpr adjustedQuery) in
    let newAggrNorm  = deriveTableNorm adjustedQuery in

    traceIfDebug debug ("----------------") $
    traceIfDebug debug (show dbAggrNorms) $
    traceIfDebug debug ("database norms    = Rows: " ++ show dbAggrNorm    ++ " | Cols: "  ++ show (map normalizeNorm dbNorms)) $
    traceIfDebug debug ("intial query norm = Rows: " ++ show queryAggrNorm ++ " | Cols: "  ++ show (normalizeNorm queryExprNorm)) $
    traceIfDebug debug ("adjust query norm = Rows: " ++ show newAggrNorm   ++ " | Cols: "  ++ show (normalizeNorm newQueryNorm)) $
    traceIfDebug debug ("scaling: " ++ show mapCol ++ "\n\t " ++ show mapLN ++ "\n\t " ++ show mapLZ ++ "\n\n") $
    traceIfDebug debug ("----------------") $
    adjustedQuery


getTableExprDataWrtOneSensVarSet :: Bool -> Bool -> (M.Map VarName B.Var) -> TableName -> TableAlias
                                    -> B.TableExpr -> (String,String,String) -> String ->
                                    Int -> NormFunction -> (S.Set B.Var) ->
                                    (TableName, TableName, B.TableExpr, (String,String,String))
getTableExprDataWrtOneSensVarSet debug policy inputMap tableName tableAlias filtQuery (sel,fr,wh) queryName index tableNorm tableSensCols =

    -- now transform the main query to a banach expression, now it is fine to use only the current table's sensitive columns
    let (queryExpr,  queryAggr)  = insertZeroSens tableSensCols filtQuery in

    -- the query will also take into account sensitive rows of the current sensitive table
    let sensRowTable  = tableName ++ "_sensRows" in
    let sensRowFilter = tableName ++ "_sensRows.ID = " ++ tableAlias ++ ".ID" in

    -- a query that creates the large cross product table
    let fr1  = fr ++ ", " ++ sensRowTable in
    let wh1  = wh ++ " AND " ++ sensRowFilter in

    traceIfDebug debug (show tableSensCols) $
    traceIfDebug debug (show queryExpr) $
    traceIfDebug debug (show tableNorm) $
    traceIfDebug debug ("---") $

    -- the query expressions defined over the large cross product table
    let adjTableExpr = deriveExprNorm debug inputMap tableSensCols [tableAlias] [tableNorm] queryExpr queryAggr in
    (tableName, queryName, adjTableExpr, (sel, fr1, wh1))


-- TODO link intermadiate variables to some column indices?
-- or apply zeroSens to some special construction?
getTableExprDataWrtIntermTable :: Bool -> Bool -> (M.Map VarName B.Var)
                                  -> B.TableExpr -> (String,String,String) -> String
                                  -> VarName -> B.Var
                                  -> (TableName, TableName, B.TableExpr, (String,String,String))
getTableExprDataWrtIntermTable debug policy inputMap filtQuery (sel,fr,wh) queryName intermediateSensVar intermediateSensCol =

    let inputTableName = varNameToTableName intermediateSensVar in
    let intermediateSensCols = S.singleton intermediateSensCol in

    -- now transform the main query to a banach expression, now it is fine to use only the current table's sensitive columns
    let (queryExpr,  queryAggr)  = insertZeroSens intermediateSensCols filtQuery in
    let tableNorm = (NF (M.fromList [(defaultNormVariable ++ intermediateSensVar, Id intermediateSensVar)]) (SelectMax (defaultNormVariable ++ intermediateSensVar))) in

    -- the query will also take into account sensitive rows of the current sensitive table
    let sensRowTable  = inputTableName ++ "_sensRows" in
    let sensRowFilter = inputTableName ++ "_sensRows.ID = " ++ inputTableName ++ ".ID" in

    -- a query that creates the large cross product table
    let fr1  = fr ++ ", " ++ sensRowTable in
    let wh1  = wh ++ " AND " ++ sensRowFilter in

    traceIfDebug debug (show intermediateSensCols) $
    traceIfDebug debug (show queryExpr) $
    traceIfDebug debug (show tableNorm) $
    traceIfDebug debug ("---") $

    -- the query expressions defined over the large cross product table
    let adjTableExpr = deriveExprNorm debug inputMap intermediateSensCols [""] [tableNorm] queryExpr queryAggr in
    (inputTableName, queryName, adjTableExpr, (sel, fr1, wh1))




-- construct input for multitable Banach analyser
-- we read the columns in the order they are given in allTableNorms, since it matches the cross product table itself
inputWrtEachTable   :: Bool -> Bool -> (M.Map VarName B.Var) ->
                       [TableAlias] -> B.TableExpr -> (String,String,String) -> String -> (M.Map TableAlias TableData) ->
                       [(TableName, TableName, B.TableExpr, (String,String,String))]
inputWrtEachTable _ _ _ [] _ _ _ _ = []
inputWrtEachTable debug policy inputMap (tableAlias : ts) filtQuery (sel,fr,wh) queryName tableMap =

    let tableData     = tableMap ! tableAlias in

    let tableNorm     = getNorm          tableData in
    let tableName     = getTableName     tableData in
    let tableSensVars = getSensCols      tableData in

    --let tableNorms1   = if policy then (let (NF as _) = tableNorm in
    --                                    let L 1.0 varNames = as ! "_nv" in
    --                                    let elems = filter (\x -> case x of {ZeroSens _ -> False ; _ -> True}) (map (as !) varNames) in
    --                                    map (\x -> NF (M.fromList [("_nv",x)]) (SelectL 1.0 "_nv")) elems)
    --                    else [tableNorm] in
    --let tableSensCols1 = if policy then map (\x -> S.singleton (inputMap ! x)) tableSensVars else [S.fromList $ map (inputMap ! ) tableSensVars] in
    let tableNorms1 = [tableNorm] in
    let tableSensCols1 = [S.fromList $ map (inputMap ! ) tableSensVars] in

    -- if there are no sensitive vars at all, we still compute the "default" norm NormZero
    let (tableSensCols, tableNorms) = if (length tableNorms1 == 0) then ([S.empty],[tableNorm]) else (tableSensCols1, tableNorms1) in 

    -- if we use policy settings, we need a separate query for each sensitive variable, even in the same table
    -- we index the table names to distinguish the queries
    let indices = [0..(length tableSensCols - 1)] in
    let entries = zipWith3 (getTableExprDataWrtOneSensVarSet debug policy inputMap tableName tableAlias filtQuery (sel,fr,wh) queryName) indices tableNorms tableSensCols in
    entries ++ inputWrtEachTable debug policy inputMap ts filtQuery (sel,fr,wh) queryName tableMap

getTableGs tableMap =
    let tableAliases = M.keys tableMap in
    let tableGsMap   = M.fromList (map (\tableAlias -> let tableData = tableMap ! tableAlias in (getTableName tableData, getGG tableData)) tableAliases) in
    M.toList tableGsMap    

addGroupToQuery :: String -> Function -> Function
addGroupToQuery grName (F as b) =
    let x  = getVarNameFromTableExpr b in
    let b' = setVarNameToTableExpr b (x ++ [grsep] ++ grName) in
    (F as b')

processQuery :: TableName -> (M.Map TableName Query) -> (M.Map String VarState) -> TableName -> TableAlias -> TableName -> 
                ([[TableName]], [[TableAlias]],[[TableName]], [GroupData], [Function], [[AExpr VarName]])
processQuery outputTableName queryMap attMap taskName tableAlias tableName =

    -- if the table is not in the query map, then it is an input table
    if not (M.member tableName queryMap) then
        ([[taskName]], [[tableAlias]], [[tableName]], [NoGR], [F (AVar tableName) (SelectPlain tableName)], [[]])
    else
        -- collect all used tables of this query
        let query@(P groupVarNames queryFuns' usedAliasMap filterFuns') = queryMap ! tableName in

        -- we assume that the group of 'group by' is a single column (can be a tuple)
        if length groupVarNames > 1 then error $ error_queryExpr_groupBy else
        if length groupVarNames > 0 && length queryFuns' /= 2 then error $ error_queryExpr_groupBy else
        let (queryFuns,queryGroups,filterFuns) = if length groupVarNames > 0 then
                                     -- use attMap and generate as many queries as there are groups
                                     let groupVarName = head groupVarNames in
                                     let groupColName = (\(F as b) -> getVarNameFromTableExpr b) (head queryFuns') in
                                     let groupVarValues = if M.member groupVarName attMap then
                                                              let varState = (attMap ! groupVarName) in
                                                              case varState of
                                                                  Range x y -> map show [x..y]
                                                                  SubSet xs -> xs
                                                                  _         -> error $ error_badAttMapBounds groupVarName varState
                                                          else error $ error_noAttMapBounds groupVarName
                                     in
                                     let n = length groupVarValues in
                                     let q1 = (\(F as b) -> F as (let x = getVarNameFromTableExpr b in SelectGroup x)) (head queryFuns') in
                                     let q2 = (last queryFuns') in
                                     let gs = GR "" groupColName groupVarName groupVarValues in
                                     let fs = filterFuns' in
                                     ([q1,q2], [gs,gs], [fs,fs])
                                 else
                                     (queryFuns', replicate (length queryFuns') NoGR, replicate (length queryFuns') filterFuns')
        in

        -- recursively, collect all subqueries and filters used to generate all used tables
        let usedAliases = M.keys usedAliasMap in
        let usedNames   = M.elems usedAliasMap in
        let subData = map (\key -> processQuery outputTableName queryMap attMap tableName key (usedAliasMap ! key)) usedAliases in
        let (taskNames', tableAliases', tableNames', subQueryGroups',subQueryFuns', subFiltFuns') = unzip6 subData in

        let taskNames      = concat taskNames'      in
        let tableAliases   = concat tableAliases'   in
        let tableNames     = concat tableNames'     in
        let subQueryGroups = concat subQueryGroups' in
        let subQueryFuns   = concat subQueryFuns'   in
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

        -- all tables used by plain subqueries will be extracted
        -- put all subquery funs and all filters together with the current query's funs and filters
        let tuple = zip5 newSubQueryFuns newSubQueryGroups newSubFiltFuns preficedTableAliases tableNames in

        let (aggrSubQueryFuns,  aggrSubQueryGroups,  aggrSubFiltFuns,  aggrSubTableAliases,  aggrSubTableNames) = unzip5 $ filter aggrQueryType tuple in
        let (               _,                   _,  plainSubFiltFuns, plainSubTableAliases, plainSubTableNames) = unzip5 $ filter (not . aggrQueryType) tuple in

        -- the filters and tableAliases of this query block are recorded for each query of the block
        let n = length newQueryFuns in
        let outputQueryFuns  = (map (\ (F qaexpr b) -> F (mergeQueryFuns newSubQueryFuns qaexpr) b) newQueryFuns) ++ aggrSubQueryFuns in
        let outputAliases    = (replicate n (concat plainSubTableAliases)) ++ aggrSubTableAliases in
        let outputNames      = (replicate n (concat plainSubTableNames))   ++ aggrSubTableNames in
        let outputGroupNames = newQueryGroups ++ aggrSubQueryGroups in
        let outputFilters    = (map (\x -> map (mergeQueryFuns newSubQueryFuns) x ++ concat plainSubFiltFuns) newFilterFuns) ++ aggrSubFiltFuns in
        -- if there are several items in the query, all the taskNames are treated as subqueries of both
        let outputTaskNames = (map (taskName :) taskNames) in

        (outputTaskNames, outputAliases, outputNames, outputGroupNames, outputQueryFuns, outputFilters)
        where aggrQueryType ((F _ b),_,_,_,_) = case b of {SelectPlain _ -> False; _ -> True}

-- assume that the tables are located in the same place where the query is
readTableData :: Bool -> String -> M.Map String VarState -> [(M.Map String VarState, Double)] -> M.Map TableName (M.Map String String) -> [TableName] -> [TableAlias] -> IO (M.Map TableAlias TableData)
readTableData policy queryPath attMap plcMaps typeMap tableNames tableAliases = do

    -- collect all norm-related table data
    -- read table sensitivities from corresponding files
    -- mapM is a standard function [IO a] -> IO [a]
    let dbNormData = if policy then
            return (constructNormData tableNames attMap plcMaps)
        else
            mapM (\tableName -> parseNormFromFile (typeMap ! tableName) $ queryPath ++ tableName ++ ".nrm") tableNames

    let badNames = filter (\t -> not (M.member t typeMap)) tableNames
    when (length badNames > 0) $ error (error_schema (M.keys typeMap) badNames)
    let tableColNames = map (\t -> M.keys (typeMap ! t)) tableNames

    (tableSensitives, tableNormFuns, tableGs) <- fmap unzip3 dbNormData
    let (_,tableSensitiveVars) = unzip tableSensitives

    -- we put table names in front of column names
    let namePrefices = map (\tableAlias -> tableAlias ++ [tsep]) tableAliases
    let fullTableColNames = zipWith (\x ys -> map (\y -> x ++ y) ys) namePrefices tableColNames
    let fullSensitiveVarNames = zipWith (\x ys -> map (\y -> x ++ y) ys) namePrefices tableSensitiveVars

    -- put all table data together
    let tableData = zipWith5 T tableNames fullTableColNames fullSensitiveVarNames tableGs tableNormFuns
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
      -- TODO some column names now come from intermediate queries
      -- we do not count these extra variables
      -- if each aggregation is allowed to be used only once, then we do not miss any counts
      map (\x -> if M.member x aliasToCountMap then aliasToCountMap M.! x else 1) colTableAliases

-- putting everything together
getBanachAnalyserInput :: ProgramOptions -> String -> String -> String -> String -> IO ([(M.Map String VarState, Double)], M.Map String VarState, String, String, [String], [(String,[(String,String)])], [(String,[Int],Bool)], [String], [(TableName, TableName, OneGroupData, B.TableExpr,(String,String,String))],[(String, Maybe Double)],[Int])
getBanachAnalyserInput args inputSchema inputQuery inputAttacker inputPolicy = do

    let debug = not (alternative args)
    let policy = policyAnalysis args

    when debug $ putStrLn $ "\\echo ##========== Query " ++ inputQuery ++ " ==============="
    let dataPath = reverse $ dropWhile (/= '/') (reverse inputSchema)

    queryFileContents <- readInput inputQuery
    (outputTableName,queryMap) <- parseQueryMap defaultOutputTableName queryFileContents
    traceIOIfDebug debug $ "queryMap:   " ++ show queryMap

    queryFileContents <- readInput inputSchema
    schemas <- parseSchemas queryFileContents
    let typeList = map extractTypes schemas
    let typeListTrimmedTypenames  = map (\(x,ys) -> (x, map (\(y1,y2) -> (y1, takeWhile (\z -> ord(z) >= 65) (map toLower y2) )) ys)) typeList
    let typeMap  = M.fromList $ map (\(x,ys) -> (x, M.fromList ys)) typeListTrimmedTypenames

    plcMaps <- parsePolicyFromFile inputPolicy
    attMap <- parseAttackerFromFile inputAttacker

    -- extract the tables that should be read from input files, take into account copies
    -- substitute intermediate queries into the aggregated query
    let (taskNames, inputTableAliases', inputTableNames', outputGroups, outputQueryFuns, filterAexprs') = processQuery outputTableName queryMap attMap "" outputTableName outputTableName
    -- by construction, the used table aliases may repeat, so we discard repetitions first
    let (inputTableAliases, inputTableNames) = unzip $ zipWith (\xs zs -> unzip $ S.toList $ S.fromList $ zip xs zs) inputTableAliases' inputTableNames' 
    let (allInputTableNames,allInputTableAliases) = unzip $ nub $ zip (concat inputTableNames) (concat inputTableAliases)

    let indexedTaskNames = zip taskNames [0..(length taskNames) - 1]
    let taskMaps = concat $ map (\(ts,i) -> (map (\t -> (t,[i]))) ts) indexedTaskNames
    let taskMap'  = M.toList $ M.fromListWith (++) $ filter (\(t,_) -> t /= "") taskMaps
    let taskMap   = map (\(t,is) -> if t == outputTableName then (t,is,True) else (t,is,False)) taskMap'

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Queries:   " ++ show outputQueryFuns
    traceIOIfDebug debug $ "Groups:   " ++ show outputGroups
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Input table names:   " ++ show allInputTableNames
    traceIOIfDebug debug $ "Input table aliases: " ++ show allInputTableAliases
    traceIOIfDebug debug $ "Task names:          " ++ show taskNames
    traceIOIfDebug debug $ "Task map:            " ++ show taskMap

    -- inputTableMap maps input table aliases to the actual table data that it reads from file (table contents, column names, norm, sensitivities)
    inputTableMap <- readTableData policy dataPath attMap plcMaps typeMap allInputTableNames allInputTableAliases

    -- the columns of the cross product are ordered according to "M.keys inputTableMap"
    let orderedTableAliases = M.keys inputTableMap

    let subExprsQ = map (\ (F aexpr _) -> getAllSubExprs False aexpr) outputQueryFuns
    let subExprsF = concat $ map (map (getAllSubExprs False)) filterAexprs'


    let intermediateColNameSetsQ = map (S.map fst) subExprsQ
    let intermediateColNameSetsF = map (S.map fst) subExprsF
    --let intermediateColNameSetsQ  = map (\ (F aexpr _) -> getAllSubExprs False aexpr) outputQueryFuns
    --let intermediateColNameSetsF  = concat $ map (map (getAllSubExprs False)) filterAexprs'
    let intermediateColNameSets = intermediateColNameSetsQ ++ intermediateColNameSetsF

    let allIntermediateGroupColNameList = map (\gr -> let (x,y) = (getGroupTableName gr, getGroupColName gr) in preficedVarName x y) outputGroups
    let allIntermediateColNameList      = map (uncurry preficedVarName) $ concat $ map S.toList intermediateColNameSets
    let allIntermediateColNameSet  = S.fromList allIntermediateColNameList
    let uniqueIntermediateColNameList = S.toList allIntermediateColNameSet
    -- TODO this check does not work since repeating values may come for the same query e.g. used in a filter expression
    -- but we still want to do an analogous check ...
    --when (length allIntermediateColNameList /= S.size allIntermediateColNameSet) $ error $ error_subQueries

    let inputColNames    = concat $ map (getUsedCols . (inputTableMap ! ) ) orderedTableAliases
    let colNames         = inputColNames ++ uniqueIntermediateColNameList ++ allIntermediateGroupColNameList
    let sensitiveVarList = concat $ map (getSensCols . (inputTableMap ! ) ) orderedTableAliases

    let fullTypeMap = foldr M.union M.empty (zipWith (\tableAlias tableName -> M.mapKeys (preficedVarName tableAlias) (typeMap ! tableName)) allInputTableAliases allInputTableNames)

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Input table map: " ++ show inputTableMap
    traceIOIfDebug debug $ "Intermediate Vars: " ++ show uniqueIntermediateColNameList
    traceIOIfDebug debug $ "Group Vars: " ++ show allIntermediateGroupColNameList
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Types1: " ++ show typeMap
    traceIOIfDebug debug $ "Types2: " ++ show fullTypeMap

    -- assign a unique integer to each column name, which is the order of this column in the cross product table
    let inputMap        = M.fromList $ zip colNames [0..length colNames - 1]
    let sensitiveColSet = S.fromList $ map (inputMap ! ) sensitiveVarList

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "All input variables:    " ++ show (M.toList inputMap)
    traceIOIfDebug debug $ "All sensitive vars:     " ++ show sensitiveVarList
    traceIOIfDebug debug $ "All sensitive cols:     " ++ show sensitiveColSet

    let filterAexprs = map (map (snd . applyAexprTypes fullTypeMap)) filterAexprs'

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "All query funs (w/o filter): " ++ show outputQueryFuns
    traceIOIfDebug debug $ "Used input table names: " ++ show inputTableNames
    traceIOIfDebug debug $ "Used input table aliases: " ++ show inputTableAliases
    traceIOIfDebug debug $ "All filters:" ++ show filterAexprs


    -- process the query blocks one by one, concatenate and reverse, so that subqueries would be processed before superqueries
    let initialSubQueryDataMap = M.fromList $ zipWith4 (\t g q f -> let qn = getQueryName q in (qn,(t,g,q,f))) inputTableAliases outputGroups outputQueryFuns filterAexprs
    let orderedQueryNames = map getQueryName outputQueryFuns
    let subQueryDataMap'   = constructQueryData initialSubQueryDataMap orderedQueryNames

    -- remove the auxiliary group-tables, as we do not need them anymore
    let commonOrderedQueryNames = filter ((\(_,_,_,_,_,_,q,_) -> isCommonQuery q) . (subQueryDataMap' M.!)) orderedQueryNames
    let subQueryDataMap         = M.filter (\(_,_,_,_,_,_,q,_) -> isCommonQuery q) $ foldl (\x y -> removeGroupFromSubQueryMap commonOrderedQueryNames x y) subQueryDataMap' orderedQueryNames

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "commonOrderedQueryNames: " ++ show commonOrderedQueryNames
    traceIOIfDebug debug $ show (M.keys subQueryDataMap')
    traceIOIfDebug debug $ show (M.keys subQueryDataMap)
    traceIOIfDebug debug $ "Subquery Map: " ++ show subQueryDataMap
    traceIOIfDebug debug $ "----------------"

    -- reconstruct the initial query
    let initialQuery = constructInitialQuery subQueryDataMap' inputTableMap (getQueryName $ head outputQueryFuns)
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Initial query: " ++ initialQuery
    traceIOIfDebug debug $ "----------------"


    let dataWrtEachTable = concat $ map (getQueryData debug policy inputMap inputTableMap fullTypeMap subQueryDataMap sensitiveVarList) (reverse commonOrderedQueryNames)

    -- additional parameters
    let tableGs = getTableGs inputTableMap
    let colTableCounts = getColTableCounts colNames allInputTableNames allInputTableAliases

    -- the last column now always marks sensitive rows
    let extColNames = colNames ++ ["sensitive"]
    let tableExprData = (plcMaps, attMap,dataPath,initialQuery, extColNames, typeList, taskMap, sensitiveVarList, dataWrtEachTable, tableGs, colTableCounts)

    -- TODO is it a proper place for table Gs?
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Table Names:" ++ show allInputTableNames
    traceIOIfDebug debug $ "Table Aliases:" ++ show allInputTableAliases
    traceIOIfDebug debug $ "Table Gs: " ++ show tableGs
    traceIOIfDebug debug $ "colTableCounts: " ++ show colTableCounts
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "tableExprData:" ++ show tableExprData
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "column names: " ++ show extColNames
    traceIOIfDebug debug $ show (length commonOrderedQueryNames)
    traceIOIfDebug debug $ show (M.size subQueryDataMap)
    traceIOIfDebug debug $ show (length dataWrtEachTable)
    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "----------------"


    -- generate the tables for intermediate aggragate queries
    let aggrIntermediateQueryFuns = filter (\(x,_) -> isAggrQuery x) $ zip (tail outputQueryFuns) (tail outputGroups)

    when debug $ putStrLn "================================="
    when debug $ putStrLn "Generating SQL statements for creating empty intermediate query tables:\n"
    let initQueries = concat $ map (\ ((F _ y),z) -> let x = getVarNameFromTableExpr y in initIntermediateAggrTableSql fullTypeMap x z) aggrIntermediateQueryFuns
    traceIOIfDebug debug $ "INIT queries : " ++ show initQueries
    sendQueriesToDbAndCommit args (initQueries)

    -- this has moved here from BanachQ since it is easier to extract pure input table names here
    let uniqueTableNames = nub $ concat inputTableNames
    let separator = delimiter args
    when debug $ putStrLn "Generating SQL statements for creating input tables:\n"
    ctss <- if (not (dbCreateTables args)) then (do return []) else
                  forM uniqueTableNames $ \ t -> do cts <- createTableSqlTyped policy dataPath separator t typeList
                                                    when debug $ putStr (concatMap (++ ";\n") cts)
                                                    return cts

    when (dbCreateTables args) $ sendQueriesToDbAndCommit args (concat ctss)

    -- return data to the banach space analyser
    return tableExprData

removeGroupFromSubQueryMap :: [String] -> M.Map String ([TableAlias],[TableAlias],[TableAlias],[Bool],[VarName],GroupData,Function, [AExpr VarName]) -> String
                              -> M.Map String ([TableAlias],[TableAlias],[TableAlias],[Bool],[VarName],GroupData,Function, [AExpr VarName])
removeGroupFromSubQueryMap qs subQueryDataMap queryName =
    let (directTableAliases,subqueryTableAliases',intermediateVarList,intermediateIsGrList,directColNames,groups,query,filterAexprs) = subQueryDataMap ! queryName in
    let subqueryTableAliases = filter (\x -> elem x qs) subqueryTableAliases' in
    M.insert queryName (directTableAliases,subqueryTableAliases,intermediateVarList,intermediateIsGrList,directColNames,groups,query,filterAexprs) subQueryDataMap

constructQueryData :: M.Map String ([TableAlias],GroupData, Function, [AExpr VarName]) -> [String] -> 
                      M.Map String ([TableAlias],[TableAlias],[TableAlias],[Bool],[VarName],GroupData,Function, [AExpr VarName])
constructQueryData _ [] = M.empty
constructQueryData initialSubQueryDataMap (queryName:qs) =

    -- first of all, collect all table aliases used by all subqueries
    let subQueryDataMap = constructQueryData initialSubQueryDataMap qs in

    -- process the current query
    let (directTableAliases,groups,query,filterAexprs) = initialSubQueryDataMap ! queryName in

    -- if some subtable is used multiple times, we still record it only once
    let directColNamesQ = (\ (F aexpr _) -> getAllAExprVars False aexpr) query in
    let directColNamesF = foldr S.union S.empty $ map (getAllAExprVars False) filterAexprs in
    let directColNames = S.toList $ S.union directColNamesQ directColNamesF in

    let subExprsQ = (\ (F aexpr _) -> getAllSubExprs False aexpr) query in
    let subExprsF = foldr S.union S.empty $ map (getAllSubExprs False) filterAexprs in

    let intermediateVarGroupListQ = S.map (\ ((x,y),b) -> (preficedVarName x y, b)) subExprsQ in
    let intermediateVarGroupListF = S.map (\ ((x,y),b) -> (preficedVarName x y, b)) subExprsF in
    let intermediateVarGroupList  = S.toList $ S.union intermediateVarGroupListQ intermediateVarGroupListF in

    let (intermediateVarList, intermediateIsCommonList)  = unzip intermediateVarGroupList in

    -- collect all table aliases used by all subqueries
    let subqueryTableAliases = concat $ map (\x -> let (ts1,ts2,_,_,_,_,_,_) = subQueryDataMap ! (varNameToQueryName x) in ts1 ++ ts2) intermediateVarList in
    let entry = (directTableAliases,subqueryTableAliases,intermediateVarList,intermediateIsCommonList,directColNames,groups,query,filterAexprs) in

    -- add the new record to the map
    M.insert queryName entry subQueryDataMap

constructInitialQuery :: M.Map String ([TableAlias],[TableAlias],[TableAlias],[Bool],[VarName],GroupData, Function, [AExpr VarName]) -> (M.Map TableAlias TableData) -> String -> String
constructInitialQuery subQueryDataMap inputTableMap queryName =

    -- process the current query
    let (directTableAliases,_,intermediateVarList,intermediateIsCommonList,directColNames,groups,query,filterAexprs) = subQueryDataMap ! queryName in

    let directTables        = map (\x -> let z = getTableName (inputTableMap ! x) in if x == z then z else z ++ " AS " ++ x) directTableAliases in
    let intermediateTables  = map varNameToTableName intermediateVarList in

    let queryStr  = queryAggrToString query in
    let filtersStr = map aexprToString filterAexprs in

    -- add groups
    let groupVar = if hasGroups groups then getGroupVarName groups ++ " AS " ++ getGroupColName groups ++ "," else "" in
    let groupBy  = if hasGroups groups then " GROUP BY " ++ getGroupColName groups else "" in
    let alias    = if isIntermediateQueryName queryName && isAggrQuery query then " AS " ++ (queryNameToVarName queryName) else "" in
    let mainSelect = "SELECT " ++ groupVar ++ queryStr ++ alias in
    let mainFrom   = intercalate ", " directTables in
    let mainWhere  = if length filtersStr == 0 then "true" else intercalate " AND " filtersStr in

    -- the groups themselves do not need to be processed, so discard them from the list of subtables
    let subIntermediateVarList = map snd $ filter (\(b,_) -> b) $ zip intermediateIsCommonList intermediateVarList in
    let subFroms = map (\x -> "(" ++ constructInitialQuery subQueryDataMap inputTableMap (varNameToQueryName x) ++ ") AS " ++ (varNameToTableName x)) subIntermediateVarList in

    -- add the subqueries to the FROM list
    (mainSelect ++ " FROM " ++ mainFrom ++ (if length subFroms > 0 then "," ++ intercalate "," subFroms else "") ++ " WHERE " ++ mainWhere ++ groupBy)


getQueryData :: Bool -> Bool -> (M.Map VarName B.Var) -> (M.Map TableAlias TableData) -> M.Map TableName String
                -> M.Map String ([TableAlias],[TableAlias],[TableAlias],[Bool],[VarName],GroupData, Function, [AExpr VarName]) -> [VarName]
                -> String
                -> [(TableName, TableName, OneGroupData, B.TableExpr, (String,String,String))]
getQueryData debug policy inputMap inputTableMap fullTypeMap queryDataMap globalSensitiveVarList queryName =

    let (_,_,_,_,_,gr,_,_) = queryDataMap ! queryName in

    traceIfDebug debug ("----------------") $
    traceIfDebug debug ("groupData " ++ show gr) $
    let groupColName = getGroupColName gr in
    let groupVarName = getGroupVarName gr in
    let groupList    = getGroupValues gr in

    concat $ map (getQueryDataForGroup debug policy inputMap inputTableMap fullTypeMap queryDataMap globalSensitiveVarList queryName groupVarName groupColName) groupList

getQueryDataForGroup :: Bool -> Bool -> (M.Map VarName B.Var) -> (M.Map TableAlias TableData) -> M.Map TableName String
                        -> M.Map String ([TableAlias],[TableAlias],[TableAlias],[Bool],[VarName],GroupData, Function, [AExpr VarName])
                        -> [VarName]
                        -> String -> String -> String -> String
                        -> [(TableName, TableName, OneGroupData, B.TableExpr, (String,String,String))]
getQueryDataForGroup debug policy inputMap inputTableMap fullTypeMap queryDataMap globalSensitiveVarList queryName groupVarName groupColName groupValue =

    let (directTableAliases,subqueryTableAliases,intermediateVarList,intermediateIsCommonList,directColNames,gr,query,filterAexprs') = queryDataMap ! queryName in

    let (filterAexprs, group, newQueryName) =
            if groupValue == defaultGroupValue then
                let x1 = filterAexprs' in
                let x2 = OneGR defaultGroupColumn defaultGroupValue in
                let x3 = queryName in
                (x1,x2,x3)
            else
                let x1 = if fullTypeMap ! groupVarName == "int" || fullTypeMap ! groupVarName == "double" then
                             -- TODO it is better to do conversion the other way around and turn int to string only
                             -- for this, we will need type information when reading attPlc file, and it is a larger change
                             (ABinary AEQint (AVar groupVarName) (AConst $ unsafePerformIO (intToString groupValue))) : filterAexprs'
                         else
                             (ABinary AEQstr (AVar groupVarName) (AText groupValue)) : filterAexprs'
                in
                let x2 = OneGR groupColName groupValue in
                let x3 = addGroupToQName queryName groupValue in
                (x1,x2,x3)
    in

    let queryStr  = queryToString query in

    -- TODO not all intermediate variables are necessarily sensitive, probably do not need to put all of them into the list
    let sensitiveVarListQ = S.toList $ (\ (F aexpr _) -> getAllAExprVars False aexpr) query in
    let sensitiveVarListF = concat $ map (S.toList . (getAllAExprVars False)) filterAexprs in
    let sensitiveVarList = (S.toList (S.intersection (S.fromList globalSensitiveVarList) (S.fromList (sensitiveVarListQ ++ sensitiveVarListF)))) ++ intermediateVarList in

    let sensitiveColList = map (inputMap ! ) sensitiveVarList in
    let sensitiveColSet  = S.fromList sensitiveColList in


    -- we filter out rows using globally public filters, since different filterings would be bad for sensitivity over all tables
    let filterSensVars = map (\x -> S.intersection sensitiveColSet (aexprToColSet inputMap True x)) filterAexprs in

    -- TODO (not important) we process the queries one by one anyway, so we may change the interface of this function
    let (filtQueryFuns, pubFilterAexprs) = addFiltersToQueries [query] filterAexprs filterSensVars in
    let filtQueryFun = head filtQueryFuns in

    let (queryExpr,queryAggr,filtQueryStr) = queryToExpr inputMap sensitiveColSet (applyQueryTypes fullTypeMap filtQueryFun) in
    let pubFilter  = map aexprToString pubFilterAexprs in

    traceIfDebug debug ("=== Processing subquery " ++ queryName ++ " ===") $

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


    -- a query that creates the large cross product table
    let directTables        = map (\x -> let z = getTableName (inputTableMap ! x) in if x == z then z else z ++ " AS " ++ x) directTableAliases in
    let intermediateTables  = map varNameToTableName intermediateVarList in
    let uniqueTables        = S.toList $ S.fromList $ directTables ++ intermediateTables in
    let sel = intercalate ", " directColNames in
    let fr  = intercalate ", " uniqueTables in
    let wh  = if length pubFilter == 0 then "true" else intercalate " AND " pubFilter in

    -- compute min/max queries using sel, fr, wh
    let minmaxQuery = case queryAggr of
                          B.SelectMin _ -> ", (SELECT MIN(" ++ queryStr ++ ") AS min, MAX(" ++ queryStr ++ ") AS max FROM " ++ fr ++ " WHERE " ++ wh ++ ") AS minmaxT"
                          B.SelectMax _ -> ", (SELECT MIN(" ++ queryStr ++ ") AS min, MAX(" ++ queryStr ++ ") AS max FROM " ++ fr ++ " WHERE " ++ wh ++ ") AS minmaxT"
                          _             -> ""
    in

    -- TODO (not important) we may take into account sensitivity of (max - min) as it was in the old version
    -- the sensitivity would depend on the currently analyzed table, so this should be moved into "inputWrtEachTable"
    --let finalTableExpr1 = applyPrecAggrTable arMin arMax queryAggr
    --let finalTableExpr1 = queryAggr in

    -- we remove the group-related intermediate varibles since we do not need them
    -- TODO this assumes that the group column name is fixed, we need a better way to distinguish group variables
    let commonIntermediateVarList = map snd $ filter (\(b,_) -> b) $ zip intermediateIsCommonList intermediateVarList in
    let commonIntermediateColList = map (inputMap ! ) commonIntermediateVarList in

    let dataWrtEachTable' = inputWrtEachTable debug policy inputMap directTableAliases queryAggr (sel,fr ++ minmaxQuery,wh) newQueryName inputTableMap
           ++ zipWith (getTableExprDataWrtIntermTable debug policy inputMap queryAggr (sel,fr ++ minmaxQuery,wh) newQueryName) commonIntermediateVarList commonIntermediateColList in

    let (allInputTableNames, allOutputTableNames, finalTableExpr, sqlQueries) = unzip4 dataWrtEachTable' in
    let dataWrtEachTable = zip5 allInputTableNames allOutputTableNames (replicate (length sqlQueries) group) finalTableExpr sqlQueries in

    traceIfDebug debug ("----------------") $
    traceIfDebug debug ("All InputTableNames:" ++ show allInputTableNames) $
    traceIfDebug debug ("All OutputTableNames:" ++ show allOutputTableNames) $
    traceIfDebug debug ("----------------") $
    traceIfDebug debug ("SELECT: " ++ show sel) $
    traceIfDebug debug ("----------------") $
    traceIfDebug debug ("FROM: " ++ show fr) $
    traceIfDebug debug ("----------------") $
    traceIfDebug debug ("WHERE: " ++ show wh) $
    traceIfDebug debug ("----------------") $

    dataWrtEachTable

