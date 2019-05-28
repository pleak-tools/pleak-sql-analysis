module GroupQ where

import Data.List
import Data.List.Split

-------------------------------
---- policy data structures ----
-------------------------------

data GroupData = GR String [String] [String] [[Either Int String]] | NoGR deriving Show
data OneGroupData = OneGR [String] [String] deriving (Show, Eq, Ord)

getGroupTableName (GR x _ _ _) = x
getGroupTableName NoGR = defaultGroupTable

getGroupColName (GR _ x _ _) = x
getGroupColName NoGR = []

getGroupVarName (GR _ _ x _) = x
getGroupVarName NoGR = []

addPrefixToGroupVar p (GR t x ys z) = GR t x (map (p++) ys) z
addPrefixToGroupVar _ NoGR       = NoGR

addPrefixToGroupTable p (GR t x y z) = GR (p++t) x y z
addPrefixToGroupTable _ NoGR       = NoGR

getGroupValues  (GR _ _ _ x) = x
getGroupValues  NoGR = []

hasGroups  (GR _ _ _ _) = True
hasGroups  NoGR = False

getOneGroupColName (OneGR x _) = x
getOneGroupValue   (OneGR _ x) = x

defaultGroupTable   = "dummy"
--defaultGroupColumn  = "groupid"
--defaultGroupVarName = "default"
--defaultGroupValue   = "\'default\'"

-- the default separator between a table name and a variable in subqueries
tsep = '.'
grsep = '#'

-- we use an improper symbol csep as query name separator, and replace it with sqlsep when communicating with the database
csep = '%'
sqlsep = '_'

-- TODO (not important) we get different separators from different sources,
-- probably we could make them the same on some earlier step
-- replace the '.' with '_'
varNameToQueryName x = map (\c -> if c == tsep then csep else c) x
varNameToTableName x = if isIntermediateQueryVar x then takeWhile (/= tsep) x else x
varNameToSubVarName x = if isIntermediateQueryVar x then tail $ dropWhile (/= tsep) x else x
varNameToTableAndSubVarName x = splitOn [tsep] x

queryNameToPreficedVarName x = if elem csep x then queryNameToTableName x ++ [tsep] ++ queryNameToVarName x else x

isIntermediateQueryName x = elem csep x
isIntermediateQueryVar x = elem tsep x

isGroupQueryVar x = elem grsep x
removeGroupFromQName x = takeWhile (/= grsep) x

queryNameToTableName x     = reverse $ tail $ dropWhile (/= csep) (reverse x)
queryNameToVarName x       = reverse $ takeWhile (/= csep) (reverse x)

queryNameToGroupName x     = if elem grsep x then tail $ dropWhile (/= grsep) (queryNameToVarName x) else queryNameToVarName x
queryNameToAggrName x      = takeWhile (/= grsep) (queryNameToVarName x)
queryNameToGroupAggrName x = (queryNameToGroupName x, queryNameToAggrName x)

preficedVarName t x = t ++ [tsep] ++ x
connectedVarName t x = t ++ [csep] ++ x
addGroupToQName t x = intercalate [grsep] (t:x)
