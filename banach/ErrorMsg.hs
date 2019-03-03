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
error_queryExpr_prefices           = "ERROR: Need to add a prefix to the columns, i.e. write \'tableName.x\' for the column \'x\' and the corresponding \'tableName\'."
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
error_queryExpr_pointDistanceLen t = "ERROR: compared points need to have the same number of coordinates " ++ show t ++ "."

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
error_badNorm   t sens = "ERROR: could not match the query norm " ++ show t ++ " agaist the variable " ++ show sens ++ ", which should be declared as numeric (i.e. be of type INT8 or FLOAT8 in the schema, and not embedded by \'l0\' in the database norm)."
error_badLNNorm t sens = "ERROR: could not match the query norm " ++ show t ++ " agaist the variable " ++ show sens ++ ", which should be declared as logarithmic (i.e. be of type INT8 or FLOAT8 in the schema, and embedded into \'ln\' construction in the database norm)."
error_badLZNorm t sens = "ERROR: could not match the query norm " ++ show t ++ " agaist the variable " ++ show sens ++ ", which should be declared as discrete (i.e. be of type \'TEXT\' datatype in the schema, and embedded by \'l0\' construction the database norm)."
error_badAggrNorm t p q  = "ERROR: can compute sensitivity for " ++ show t ++ " only w.r.t row norm l_" ++ p ++ ", not l_" ++ q ++ "."

--subquery related errors
error_noSubquery q1 q2 qmap = "ERROR: the query " ++ q1 ++ " uses " ++ q2 ++ " as subquery, but it is missing from " ++ show qmap ++ "."

--the next error is not used anymore
error_verifyNorm t  = "INTERNAL ERROR: Could not prove that the database norm is at least as large as the query norm for sensitivity w.r.t. table " ++ show t

-- policy analysis error messages
error_attackerBreaksEverything = "ERROR: impossible to enforce policy against current attacker definition."
error_badAttackerPolicyCombination attState plcState = "ERROR: the combination of attacker state " ++ show attState ++ " and sensittive data state " ++ show plcState ++ " is not supported."
err_badAttackerPolicy_n x     = "ERROR: negative number of choices in " ++ show x
err_badAttackerPolicy_range x = "ERROR: lower bound is smaller than upper bound in " ++ show x
err_badAttackerPolicy_Pr x    = "ERROR: the probbailities should be nonnegative and sum up to 1 in " ++ show x
err_badAttackerPolicy x       = "ERROR: unsupported attacker state " ++ show x
err_badPolicy_r x             = "ERROR: negative radius in sensitive data state " ++ show x
err_badPolicy x               = "ERROR: unsupported sensitive data state " ++ show x

error_unboundedDataType t = "ERROR: data type " ++ t ++ " cannot be included into policy yet."
error_badPolicyFormat preficedVar = "ERROR: policy format error, \"" ++ preficedVar ++ "\" is expected to be of the form \"tableName.varName\""
error_badSetPolicyFormat xs1 xs2 = "ERROR: policy format error, should not use strings " ++ show xs1 ++ " and integers " ++ show xs2 ++ " in one set."
error_badPolicySensRows vs    = "ERROR: the sensitive rows should be listed as \'Range a b\', but we got " ++ show vs ++ " instead."

-- groupBy-related messages
error_noAttMapBounds x = "ERROR: no set of possible values is specified for " ++ x ++ ", which is essential for GROUP BY queries. Specify \'set x1 ... xn\' or \'range x y\' in the attacker file."
error_badAttMapBounds x t = "ERROR: bad set of possible values " ++ show t ++ " for " ++ x ++ ", which is essential for GROUP BY queries. Use \'set x1 ... xn\' or \'range x y\' in the attacker file. Note that GROUP BY variables need to have table name prefices."
error_noCSGroupSupport = "ERROR: GROUP BY is not support in combined sensitivity. Use plain derivative sensitivity (i.e. without \'-c\' parameter)."
