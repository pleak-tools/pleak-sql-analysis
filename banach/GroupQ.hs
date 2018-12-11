module GroupQ where

-------------------------------
---- policy data structures ----
-------------------------------

data GroupData = GR String String [String] | NoGR deriving Show
data OneGroupData = OneGR String String deriving Show

getGroupColName (GR x _ _) = x
getGroupColName NoGR = defaultGroupColumn

getGroupVarName (GR _ x _) = x
getGroupVarName NoGR = defaultGroupVarName

addPrefixToGroupVarName p (GR x y z) = GR x (p++y) z
addPrefixToGroupVarName _ NoGR       = NoGR

getGroupValues  (GR _ _ x) = x
getGroupValues  NoGR = [defaultGroupValue]

hasGroups  (GR _ _ _) = True
hasGroups  NoGR = False

getOneGroupColName (OneGR x _) = x
getOneGroupValue   (OneGR _ x) = x

defaultGroupColumn  = "groupid"
defaultGroupVarName = "default"
defaultGroupValue   = "\'default\'"

-- the default separator between a table name and a variable in subqueries
tsep = '.'
csep = '_'
grsep = '#'
