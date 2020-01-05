module ErrorMsg where

import qualified Data.Map as M

-- map element sampling with a more readable error message
-- requires keys and values to be showable
(!) :: (Show k, Show a, Ord k) => M.Map k a -> k -> a
(!) xs x = if M.member x xs then xs M.! x else error $ error_mapElem x xs --(M.keys xs)

-- if the data is showable, let us show it in the error
at1 :: (Show a) => [a] -> Int -> a
at1 xs x = if x < length xs then xs !! x else error $ error_arrElem x xs

-- otherwise, let us just say that "something is wrong"
at2 :: [a] -> Int -> a
at2 xs x = if x < length xs then xs !! x else error $ error_arrElem x "(an unshowable array)"

equal :: (Ord a) => a -> a -> Bool
equal x y = (x == y)

notequal :: (Ord a) => a -> a -> Bool
notequal x y = (x /= y)

divide :: (Fractional a) => a -> a -> a
divide x y = x / y

--------------------------------------------------------
errorTag   = "ERROR:"
inErrTag   = "INTERNAL ERROR:"
warningTag = "WARNING:"


-- some hardcoded error message
error_negativeNoise = errorTag ++ " NEGATIVE NOISE LEVEL - differential privacy could not be achieved, try to increase epsilon!"
error_emptyTable    = errorTag ++ " Cannot analyse sensitivity of an empty table."

-- the term t contains the error message generated inside megaparsec
error_parseSqlQuery s t = errorTag ++ " Could not parse the query from file " ++ show s ++ "\nError details: " ++ t
error_parseQuery    s t = errorTag ++ " Could not parse the query from file " ++ show s ++ "\nError details: " ++ t
error_parseNorm     s t = errorTag ++ " Could not parse the norm from file "  ++ show s ++ "\nError details: " ++ t
error_parsePolicy     s t = errorTag ++ " Could not parse policy from file "  ++ show s ++ "\nError details: " ++ t
error_parseAttacker   s t = errorTag ++ " Could not parse attacker settings from file "  ++ show s ++ "\nError details: " ++ t
error_parseData     s   = errorTag ++ " Could not parse the data table from file " ++ show s

-- unsupported SQL syntax
error_filterExpr ord b   = errorTag ++ " Unsupported filter for relation " ++ show ord ++ " and aggregator " ++ show b
error_filterExprConstr t = errorTag ++ " Unknown filter construction " ++ show t

error_queryExpr t   = errorTag ++ " Unsupported term in the expression " ++ show t
error_queryExpr_prefices t         = errorTag ++ " Need to add a prefix to the columns, i.e. write \'tableName.x\' for the column \'x\' and the corresponding \'tableName\'. We see " ++ show t ++ " and do not know the source table."
error_queryExpr_unnamed t          = errorTag ++ " Need to define an alias for intermediate query column " ++ show t
error_queryExpr_syntax t           = errorTag ++ " Unsupported query syntax " ++ show t
error_queryExpr_compStr t          = errorTag ++ " We cannot yet compare two sensitive strings and analyse " ++ show t
error_queryExpr_groupBy            = errorTag ++ " GROUP BY is allowed only for queries of the form SELECT x1,...,xn, y FROM t GROUP BY x1,...,xn"
error_queryExpr_aggrInterm t       = errorTag ++ " Aggregator " ++ show t ++ " not supported in the intermediate tables."
error_queryExpr_aggrFinal t        = errorTag ++ " Aggregator " ++ show t ++ " not supported in the final query."
error_queryExpr_aggrAvg            = errorTag ++ " Aggregator AVG is supported only without sensitive filters."
error_queryExpr_singleColumn       = errorTag ++ " Only a single output in the final query is supported."
error_queryExpr_undefinedVars t    = error_queryExpr t ++ ",\n some of its arguments are undefined."
error_queryExpr_missingInputVars t = error_queryExpr t ++ ",\n the input has to be an input table column."
error_queryExpr_missingAsgnVars t  = error_queryExpr t ++ ",\n the input has to be an expression."
error_queryExpr_notAllInputVars t  = error_queryExpr t ++ ",\n all the inputs have to be input table columns."
error_queryExpr_notAllAsgnVars t   = error_queryExpr t ++ ",\n all the inputs have to be expressions."
error_queryExpr_repeatingVars t    = error_queryExpr t ++ ",\n variables are repeating in different args of the term."
error_queryExpr_pointDistanceLen t = errorTag ++ " compared points need to have the same number of coordinates " ++ show t ++ "."

error_noColNames = errorTag ++ " all columns of intermediate tables need to be named, use SELECT ... AS ..."

-- type errors
error_typeDoesNotExist s = errorTag ++ " data type \'" ++ s ++ "\' is not supported."
error_tableTypeError x varType = errorTag ++ " table value " ++ show x ++ " is not of type " ++ varType ++ " as schema states."
error_badTypes x y = errorTag ++ " cannot compare the types " ++ show x ++ " and " ++ show y ++ "."

-- schema-related errors
error_schema good bad = errorTag ++ " need to provide schemas for input tables " ++ show bad ++ ", found schemas only for " ++ show good ++ "."
error_schema_bad_var t x xs = errorTag ++ " the data file of table " ++ t ++ " contains variable " ++ x ++ ", but its schema only contains columns " ++ show xs ++ "."

-- attacker knowledge related errors
warning_badAttackerVars xs = warningTag ++ " the variables " ++ show xs ++ " specified in attacker knowledge file are not used by the query, so they will be ignored."
error_badAttackerTypes  xs = errorTag   ++ " the types of variables " ++ show xs ++ " specified in attacker knowledge are not compatible with the schema."

-- internall errors that may come due to bugs in the analyser itself
error_internal                         = inErrTag ++ " Some internal analyser problem: "
error_internal_queryExprFilter t       = error_internal ++ "\n query expression " ++ show t ++ " identified as a filter."
error_internal_normRegroup             = error_internal ++ "\n unexpected norm regroup problem."
error_internal_extractScaling t        = error_internal ++ "\n cannot extract scaling from " ++ show t
error_internal_sensitivityMatrix n1 n2 = error_internal ++ "\n " ++ show n2 ++ " tables, but " ++ show n1 ++ " columns in sensitivity matrix."
error_internal_fillMissing x i xs      = error_internal ++ "case x < i in fillMissing: " ++ show x ++ " < " ++ show i ++ " in " ++ show xs
error_internal_badlength z xs ys       = error_internal ++ " the following data in " ++ show z ++ " should be of equal length: " ++ show xs ++ " and " ++ show ys

error_internal_empty_taskname t        = error_internal ++ " the name of the output table " ++ t ++ " was not found in the query map."

error_mapElem x xs     = inErrTag ++ " Element " ++ show x ++ " is not in the map " ++ show xs
error_arrElem x xs     = inErrTag ++ " Index " ++ show x ++ " is out of bounds in array " ++ show xs

-- norm-related errors
-- the first parameter is the norm itself, which is not readable to the user anyway
-- TODO we do not want to mention the 'norm' in the policy analysis (ideally, policy analysis should not produce this message)
error_badNorm   _ sens = errorTag ++ " could not construct the norm w.r.t. the variable " ++ show sens ++ ", which should be declared as numeric (i.e. be of type INT8 or FLOAT8 in the schema, and not embedded by \'l0\' in the database norm)."
error_badLNNorm _ sens = errorTag ++ " could not construct the norm w.r.t. the variable " ++ show sens ++ ", which should be declared as logarithmic (i.e. be of type INT8 or FLOAT8 in the schema)."
error_badLZNorm _ sens = errorTag ++ " could not construct the norm w.r.t. the variable " ++ show sens ++ ", which should be declared as discrete (i.e. be of type \'TEXT\' in the schema, and embedded by \'l0\' construction the database norm)."

-- this error message is not used anymore
error_badAggrNorm t p q  = errorTag ++ " can compute sensitivity for " ++ show t ++ " only w.r.t row norm l_" ++ p ++ ", not l_" ++ q ++ "."

error_badNormVariable policy x xs = errorTag ++ " the " ++ (if policy then "policy" else "norm") ++ " description contains variable " ++ x ++ ", but the schema only contains columns " ++ show xs ++ "."

--subquery related errors
warning_minMaxSubQueries = warningTag ++ " grouping in min/max queries leaks whether a group is empty."
error_subQueries = errorTag ++ " subqueries cannot share variables with the main query or other subqueries."
error_noSubquery q1 q2 qmap = errorTag ++ " the query " ++ q1 ++ " uses " ++ q2 ++ " as subquery, but it is missing from " ++ show qmap ++ "."

--the next error is not used anymore
error_verifyNorm t  = inErrTag ++ " Could not prove that the database norm is at least as large as the query norm for sensitivity w.r.t. table " ++ show t

-- policy analysis error messages
error_attackerBreaksEverything = errorTag ++ " impossible to enforce policy against current attacker definition."
error_badAttackerPolicyCombination attState plcState = errorTag ++ " the combination of attacker state " ++ show attState ++ " and sensittive data state " ++ show plcState ++ " is not supported."
err_badAttackerPolicy_n x     = errorTag ++ " negative number of choices in " ++ show x
err_badAttackerPolicy_range x = errorTag ++ " lower bound is smaller than upper bound in " ++ show x
err_badAttackerPolicy_Pr x    = errorTag ++ " the probabilities should be nonnegative and sum up to 1 in " ++ show x
err_badAttackerPolicy_normal x = errorTag ++ " normal distribution has format 'normal mu sigma^2', where sigma^2 should be >= 0, but we have " ++ show x
err_badAttackerPolicy x       = errorTag ++ " unsupported attacker state " ++ show x
err_badPolicy_r x             = errorTag ++ " bad radius in sensitive data state " ++ show x
err_badPolicy x               = errorTag ++ " unsupported sensitive data state " ++ show x

error_unboundedDataType t = errorTag ++ " data type " ++ t ++ " cannot be included into policy yet."
error_badPolicyFormat preficedVar = errorTag ++ " policy format error, \"" ++ preficedVar ++ "\" is expected to be of the form \"tableName.varName\""
error_badPolicyFormatEmptyVars = errorTag ++ " policy format error, an empty variable list is being approximated"
error_badPolicyFormatLpMixedTables prefices = errorTag ++ " columns of different tables \"" ++ show prefices ++ "\" cannot be combined into a vector in sensitive data description\""
error_badPolicyFormatLpDiscrete xs = errorTag ++ " discrete table columns \"" ++ show xs ++ "\" cannot be combined into a vector in sensitive data description\""
error_badPolicyFormatUnknownSetVar x mp = errorTag ++ " data contains the value " ++ show x ++ " whose probability has not been defined in " ++ show mp ++ "."
error_badPolicyFormatBadRange x lb ub = errorTag ++ show x ++ " is out of input range (" ++ show lb ++ "," ++ show ub ++ ")."
error_badPolicyString x = errorTag ++ " actual data " ++ show x ++ " is a string, but we need a double."
error_badPolicyDouble x = errorTag ++ " actual data " ++ show x ++ " is a double, but we need a string."
error_badSetPolicyFormat xs1 xs2 = errorTag ++ " policy format error, should not use strings " ++ show xs1 ++ " and integers " ++ show xs2 ++ " in one set."
error_badPolicySensRows vs    = errorTag ++ " the sensitive rows should be listed as \'Range a b\', but we got " ++ show vs ++ " instead."

-- groupBy-related messages
error_badGroupType groupName groupValue groupType = errorTag ++ " bad group by " ++ groupName ++ " the value " ++ groupValue ++ " is not of type " ++ groupType ++ "."
error_noAttMapBounds x = errorTag ++ " no set of possible values is specified for " ++ x ++ ", which is essential for GROUP BY queries. Specify \'set x1 ... xn\' or \'range x y\' in the attacker file."
error_floatAttMapBounds x t = errorTag ++ " cannot group by a floating-point value " ++ show x ++ " from distribution " ++ show t ++ " in a GROUP BY query."
error_badAttMapBounds x t = errorTag ++ " bad set of possible values " ++ show t ++ " for " ++ x ++ ", which is essential for GROUP BY queries. Use \'set x1 ... xn\' or \'range x y\' in the attacker file. Note that GROUP BY variables need to have table name prefices."
error_noCSGroupSupport = errorTag ++ " GROUP BY is not support in combined sensitivity. Use plain derivative sensitivity (i.e. without \'-c\' parameter)."

-- rangeutils errors
error_badRangeAexpr aexpr = error_internal ++ " computation of range undefined for Aexpr " ++ show aexpr
