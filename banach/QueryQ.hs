module QueryQ where

import Control.Monad (void)
import Data.Bits
import Data.Either
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Void
--import Debug.Trace

import qualified Banach as B
import ErrorMsg
import ExprQ
import AexprQ

type TableName  = String
type TableAlias = String

-------------------------------
---- Query data structures ----
-------------------------------

-- a function consists of a unit expression "AExpr VarName" and returns a single "TableExpr"
-- an assigment is identitified by the assigned variable, we assume the variables are not reused
-- each assignment maps a variable to an expression
data Function
  = F (AExpr VarName) TableExpr
  deriving (Show)

data NormFunction
  = NF (M.Map VarName Expr) TableExpr
  deriving (Show)

-- the format of the query
--   "[String]"         is the list of columns by which the result should be grouped
--   "[Function]"       is the list of the queried function itself (SELECT x)
--   "[TableName]"      is the list of input tables that are used in the query (FROM x)
--   "[TableAlias]"     is the list of table names that are used in the query (FROM ... AS x)
--   "[AExpr VarName]"  is the list of filters used in the query (WHERE x)
data Query
  = P [String] [Function] (M.Map TableAlias TableName) [AExpr VarName]
  deriving (Show)

data TableData =
    -- content initColNames taggedColNames norms aggrNorms sensRows sensCols originalTablename 
    T B.Table [VarName] [VarName] NormFunction [[Int]] [VarName] TableName
  deriving Show

getTableValues   (T x _ _ _ _ _ _) = x
getColNames      (T _ x _ _ _ _ _) = x
getTagColNames   (T _ _ x _ _ _ _) = x
getNorm          (T _ _ _ x _ _ _) = x
getSensitiveRows (T _ _ _ _ x _ _) = x
getSensitiveCols (T _ _ _ _ _ x _) = x
getTableName     (T _ _ _ _ _ _ x) = x

getQueryGroupNames (P x _ _ _) = x
getQueryFunctions  (P _ x _ _) = x
getQueryAliasMap   (P _ _ x _) = x
getQueryFilters    (P _ _ _ x) = x

concatMaps :: (Ord k) => [M.Map k a] -> M.Map k a
concatMaps xs = foldr M.union M.empty xs


------------------------------------------------
-- some important constants that are (or have been) used multiple times
one    = AConst   1.0
half   = AConst   0.5
oneNeg = AConst (-1.0)
two    = AConst   2.0

inf    = ABinary ASub (AText "minmaxT.max") (AText "minmaxT.min")
infNeg = ABinary ASub (AText "minmaxT.min") (AText "minmaxT.max")

infMax = AText "minmaxT.max"
infMin = AText "minmaxT.min"

------------------------------------------------
---- Executing public parts of an SQL query ----
------------------------------------------------

-- put the columns of all input tables together
getAllColumns :: M.Map TableAlias TableData -> ([VarName], [VarName], [VarName], [VarName])
getAllColumns tableMap =

    let tableAliases = M.keys tableMap in

    let allTableVars     = map ( (\t -> let prefix = (getTableName t) ++ "." in map (prefix ++ ) (getColNames t)) . (tableMap ! ) ) tableAliases in
    let allInputVars     = map (getColNames .      (tableMap ! ) ) tableAliases in
    let allTaggedVars    = map (getTagColNames .   (tableMap ! ) ) tableAliases in
    let allSensitiveVars = map (getSensitiveCols . (tableMap ! ) ) tableAliases in

    -- the input variables are concatenated in the order of tables, since each of them describes a column
    let tableVarList     = concat allTableVars in
    let inputVarList     = concat allInputVars in
    let tagInputVarList  = concat allTaggedVars in
    let sensitiveVarList = concat allSensitiveVars in

    (inputVarList, tableVarList, tagInputVarList, sensitiveVarList)

---------------------------------------------
-- TODO we will not need the next cross product functions in the new version

-- finds a cross product of N lists, applies the operation 'f' to elements that come together
crossProduct :: (a -> a -> a) -> [a] -> [[a]] -> [a]
crossProduct f start = foldr (\xs ys -> [f x y | x <- xs, y <- ys]) start

tableJoin :: [B.Table] -> B.Table
tableJoin xs = crossProduct (++) [[]] xs

vectorJoin :: [[[a]]] -> [[a]]
vectorJoin xss = crossProduct (++) [[]] xss

charVecJoin :: [[Bool]] -> [Bool]
charVecJoin xs = crossProduct (||) [False] xs

-- compute table data for a cross product
getTableCrossProductTable :: M.Map TableAlias TableData -> B.Table
getTableCrossProductTable tableMap =

    -- find the cross product of all used tables
    let tableAliases = M.keys tableMap in
    let allTables        = map (getTableValues .   (tableMap ! ) ) tableAliases in
    let crossProductTable = tableJoin allTables in
    crossProductTable

--------------------------------------------------------------
-- add longer prefices to column names in compound queries

updateQueryVariableNames :: (S.Set String) -> TableAlias -> Function -> Function
updateQueryVariableNames fullTablePaths prefix (F aexpr b) =
    let aexpr' = updatePreficesAexpr fullTablePaths prefix aexpr in
    let b'     = updatePreficesTableExpr fullTablePaths prefix b in
    F aexpr' b'

applyQueryTypes :: (M.Map VarName String) -> Function -> Function
applyQueryTypes typeMap (F aexpr b) =
    let aexpr' = snd $ applyAexprTypes typeMap aexpr in
    F aexpr' b

updateAExprVariableNames :: (S.Set String) -> TableAlias -> AExpr VarName -> AExpr VarName
updateAExprVariableNames fullTablePaths prefix aexpr = updatePreficesAexpr fullTablePaths prefix aexpr

queryToExpr :: (M.Map VarName B.Var) -> (S.Set B.Var) -> Function -> (B.Expr, B.TableExpr, String)
queryToExpr inputMap allSensitiveCols (F aexpr y) =
    let x = extractArg y in
    let asgnMap = aexprToExpr x $ aexprNormalize aexpr in
    let queryExpr = snd $ exprToBExpr allSensitiveCols inputMap asgnMap (asgnMap ! x) in
    let queryStr  = exprToString True asgnMap (asgnMap ! x) in
    let queryAggr = queryArg y [queryExpr] in
    (queryExpr,queryAggr,queryStr)

queryToString :: Function -> String
queryToString (F aexpr y) =
    let x = extractArg y in
    let asgnMap = aexprToExpr x $ aexprNormalize aexpr in
    exprToString True asgnMap (asgnMap ! x)

insertZeroSens :: (S.Set B.Var) -> B.TableExpr -> (B.Expr, B.TableExpr)
insertZeroSens tableSensitiveCols tableExpr =
    markTableExprCols tableSensitiveCols tableExpr

---------------------------------------------
-- filtering

-- applies the list of filters to a table (computes AND of all filters for each row)
-- if all variables that are used in the filter are non-sensitive, add the filter directly to the initial SQL query
-- if at least one variable is sensitive, use a sigmoid or something similar, it depends on the filter and the aggregating function
addFiltersToQueries :: [Function] -> [AExpr VarName] -> [S.Set B.Var] -> ([Function], [AExpr VarName])
addFiltersToQueries queries filts fvars = 
    let (pubPart, privPart) = partition (\ (_,fvar) -> S.size fvar == 0) (zip filts fvars) in
    let pubFilters  = map fst pubPart in
    let privFilters = map fst privPart in
    let newQueries = if length privFilters > 0 then
                         let privFilter = if length privFilters > 1 then AAnds privFilters else head privFilters in
                         map (rewriteQuery privFilter) queries
                     else
                         queries
    in (newQueries, pubFilters)

rewriteQuery :: AExpr VarName -> Function -> Function
rewriteQuery faexpr (F qaexpr qaggr) =

    case qaggr of

        -- for counting, take the filter output and compute sum of the results
        SelectCount qx ->
                 let aRw = faexpr in
                 let bRw = SelectSumBin qx in
                 F aRw bRw

        -- for sum and L-norms, we just multiply the value by the filter output
        SelectSum qx ->
                 let aRw = ABinary AMult faexpr qaexpr in
                 let bRw = SelectSum qx in
                 F aRw bRw

        SelectL p qx ->
                 let aRw = ABinary AMult faexpr qaexpr in
                 let bRw = SelectL p qx in
                 F aRw bRw

        -- for product, take 1 + b*(qx - 1), where b is the filter output, so the values that are filtered out become 1
        -- this is not good to be sigmoid-approximated since the error becomes too large with multiplication
        SelectProd qx ->
                 let aRw = ABinary AAdd one (ABinary AMult faexpr (ABinary AAdd qaexpr oneNeg)) in
                 let bRw = SelectProd qx in
                 F aRw bRw

        -- for min/max, add/subtract a large quantity from the values that are filtered out, so that they would be ignored
        SelectMax qx ->
                 --let aRw = ABinary AAdd qaexpr (ABinary AMult (ABinary ASub faexpr one) inf) in
                 let aRw = ABinary AMin qaexpr (ABinary AAdd infMin (ABinary AMult inf faexpr)) in
                 let bRw = SelectMax qx in
                 F aRw bRw

        SelectMin qx ->
                 --let aRw = ABinary AAdd qaexpr (ABinary AMult (ABinary ASub one faexpr) inf) in
                 let aRw = ABinary AMax qaexpr (ABinary AAdd infMax (ABinary AMult infNeg faexpr)) in
                 let bRw = SelectMin qx in
                 F aRw bRw

        _ -> error $ error_filterExprConstr qaggr




