module ErrorMsg where

import qualified Data.Map as M

-- map element sampling with a more readable error message
-- requires keys and values to be showable
(!) :: (Show k, Show a, Ord k) => M.Map k a -> k -> a
(!) xs x = if M.member x xs then xs M.! x else error $ error_mapElem x (M.keys xs)

-- if the data is showable, let us show it in the error
at1 :: (Show a) => [a] -> Int -> a
at1 xs x = if x < length xs then xs !! x else error $ error_arrElem x xs

-- otherwise, let us just say that "something is wrong"
at2 :: [a] -> Int -> a
at2 xs x = if x < length xs then xs !! x else error $ error_arrElem x "(an unshowable array)"

equal :: (Ord a) => a -> a -> Bool
equal x y = (x == y)

--------------------------------------------------------
-- some hardcoded error message
error_negativeNoise = "ERROR: NEGATIVE NOISE LEVEL - differential privacy could not be achieved, try to increase epsilon!"
error_emptyTable    = "ERROR: Cannot analyse sensitivity of an empty table."

-- the term t contains the error message generated inside megaparsec
error_parseSqlQuery s t = "ERROR: Could not parse the query from file " ++ show s ++ "\nError details: " ++ t
error_parseQuery    s t = "ERROR: Could not parse the query from file " ++ show s ++ "\nError details: " ++ t
error_parseNorm     s t = "ERROR: Could not parse the norm from file "  ++ show s ++ "\nError details: " ++ t
error_parsePolicy     s t = "ERROR: Could not parse policy from file "  ++ show s ++ "\nError details: " ++ t
error_parseAttacker   s t = "ERROR: Could not parse attacker settings from file "  ++ show s ++ "\nError details: " ++ t
error_parseData     s   = "ERROR: Could not parse the data table from file " ++ show s

-- unsupported SQL syntax
error_filterExpr ord b   = "ERROR: Unsupported filter for relation " ++ show ord ++ " and aggregator " ++ show b
error_filterExprConstr t = "ERROR: Unknown filter construction " ++ show t

error_queryExpr t   = "ERROR: Unsupported term in the expression " ++ show t
error_queryExpr_unnamed t          = "ERROR: Need to define an alias for intermediate query column " ++ show t
error_queryExpr_syntax t           = "ERROR: Unsupported query syntax " ++ show t
error_queryExpr_groupBy            = "ERROR: GROUP BY is allowed only for queries of the form SELECT x1,...,xn, y FROM t GROUP BY x1,...,xn"
error_queryExpr_aggrInterm t       = "ERROR: Aggregator " ++ show t ++ " not supported in the intermediate tables."
error_queryExpr_aggrFinal t        = "ERROR: Aggregator " ++ show t ++ " not supported in the final query."
error_queryExpr_singleColumn       = "ERROR: Only a single output in the final query is supported."
error_queryExpr_undefinedVars t    = error_queryExpr t ++ ",\n some of its arguments are undefined."
error_queryExpr_missingInputVars t = error_queryExpr t ++ ",\n the input has to be an input table column."
error_queryExpr_missingAsgnVars t  = error_queryExpr t ++ ",\n the input has to be an expression."
error_queryExpr_notAllInputVars t  = error_queryExpr t ++ ",\n all the inputs have to be input table columns."
error_queryExpr_notAllAsgnVars t   = error_queryExpr t ++ ",\n all the inputs have to be expressions."
error_queryExpr_repeatingVars t    = error_queryExpr t ++ ",\n variables are repeating in different args of the term."

error_noColNames = "ERROR: all columns of intermediate tables need to be named, use SELECT ... AS ..."
error_typeDoesNotExist s = "ERROR: data type \'" ++ s ++ "\' is not supported."
error_tableTypeError x varType = "ERROR: table value " ++ show x ++ " is not of type " ++ varType ++ "."
error_badTypes x y = "ERROR: cannot compare the types " ++ show x ++ " and " ++ show y ++ "."

error_subQueries = "ERROR: subqueries cannot share variables with the main query or other subqueries."
error_schema good bad = "ERROR: need to provide schemas for input tables " ++ show bad ++ ", found schemas only for " ++ show good ++ "."

-- internall errors that may come due to bugs in the analyser itself
error_internal      = "INTERNAL ERROR: Some internal analyser problem: "
error_internal_queryExprFilter t       = error_internal ++ "\n query expression " ++ show t ++ " identified as a filter."
error_internal_normRegroup             = error_internal ++ "\n norm regroup problem."
error_internal_extractScaling t        = error_internal ++ "\n cannot extract scaling from " ++ show t
error_internal_sensitivityMatrix n1 n2 = error_internal ++ "\n " ++ show n2 ++ " tables, but " ++ show n1 ++ " columns in sensitivity matrix."
error_internal_fillMissing x i xs      = "case x < i in fillMissing: " ++ show x ++ " < " ++ show i ++ " in " ++ show xs

error_mapElem x xs     = "INTERNAL ERROR: Element " ++ show x ++ " is not in " ++ show xs
error_arrElem x xs     = "INTERNAL ERROR: Index " ++ show x ++ " is out of bounds in array " ++ show xs
error_badNorm   t sens = "ERROR: the database norm " ++ show t ++ " does not contain the variable " ++ show sens ++ " declared as sensitive."
error_badLNNorm t sens = "ERROR: the database norm " ++ show t ++ " does not contain the variable " ++ show sens ++ " declared as sensitive."
error_badLZNorm t sens = "ERROR: the database norm " ++ show t ++ " does not contain the variable " ++ show sens ++ " declared as sensitive."
error_badAggrNorm t p q  = "ERROR: can compute sensitivity for " ++ show t ++ " only w.r.t row norm l_" ++ p ++ ", not l_" ++ q ++ "."

--subquery related errors
error_noSubquery q1 q2 qmap = "ERROR: the query " ++ q1 ++ " uses " ++ q2 ++ " as subquery, but it is missing from " ++ show qmap ++ "."

--the next error is not used anymore
error_verifyNorm t  = "INTERNAL ERROR: Could not prove that the database norm is at least as large as the query norm for sensitivity w.r.t. table " ++ show t

-- policy analysis error messages
error_attackerBreaksEverything = "ERROR: impossible to enforce policy against current attacker definition."
error_badAttackerPolicyCombination attState plcState = "INTERNAL ERROR: no implementation for attacker state " ++ show attState ++ " and policy state " ++ show plcState ++ "."
error_unboundedDataType t = "ERROR: data type " ++ t ++ " cannot be included into policy yet."
error_badPolicyFormat preficedVar = "ERROR: policy format error, \"" ++ preficedVar ++ "\" is expected to be of the form \"tableName.varName\""

-- groupBy-related messages
error_noAttMapBounds x = "ERROR: no set of possible values is specified for " ++ x ++ ", which is essential for GROUP BY queries. Specify \'set x1 ... xn\' or \'range x y\' in the attacker file."
error_badAttMapBounds x t = "ERROR: bad set of possible values " ++ show t ++ " for " ++ x ++ ", which is essential for GROUP BY queries. Use \'set x1 ... xn\' or \'range x y\' in the attacker file. Note that GROUP BY variables need to have table name prefices."
error_noCSGroupSupport = "ERROR: GROUP BY is not support in combined sensitivity. Use plain derivative sensitivity (i.e. without \'-c\' parameter)."
