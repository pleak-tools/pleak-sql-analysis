module ErrorMsg where

import Prelude hiding ((!!))
import qualified Prelude as P
import qualified Data.Map as M

-- map element sampling with a more readable error message
-- requires keys and values to be showable
(!) :: (Show k, Show a, Ord k) => M.Map k a -> k -> a
(!) xs x = if M.member x xs then xs M.! x else error $ error_arrElem x (M.keys xs)

(!!) :: (Show a) => [a] -> Int -> a
(!!) xs x = if x < length xs then xs P.!! x else error $ error_arrElem x xs
--------------------------------------------------------
-- some hardcoded error message

error_emptyTable = "ERROR: Cannot analyse sensitivity of an empty table."

-- the term t contains the error message generated inside megaparsec
error_parseSqlQuery s t = "ERROR: Could not parse the query from file " ++ show s ++ "\nError details: " ++ t
error_parseQuery    s t = "ERROR: Could not parse the query from file " ++ show s ++ "\nError details: " ++ t
error_parseNorm     s t = "ERROR: Could not parse the norm from file " ++ show s ++ "\nError details: " ++ t
error_parseData     s   = "ERROR: Could not parse the data table from file " ++ show s

-- unsupported SQL syntax
error_filterExpr ord b   = "ERROR: Unsupported filter for relation " ++ show ord ++ " and aggregator " ++ show b ++ "."
error_filterExprConstr t = "ERROR: Unknown filter construction " ++ show t ++ "."

error_queryExpr t   = "ERROR: Unsupported term in the expression " ++ show t
error_queryExpr_syntax t           = "ERROR: Unsupported query syntax " ++ show t ++ "."
error_queryExpr_groupBy            = "ERROR: GROUP BY is not supported yet."
error_queryExpr_aggrInterm t       = "ERROR: Aggregator " ++ show t ++ " not supported in the intermediate tables."
error_queryExpr_aggrFinal t        = "ERROR: Aggregator " ++ show t ++ " not supported in the final query."
error_queryExpr_singleColumn       = "ERROR: Only a single output in the final query is supported."
error_queryExpr_undefinedVars t    = error_queryExpr t ++ ",\n some if its arguments are undefined."
error_queryExpr_missingInputVars t = error_queryExpr t ++ ",\n the input has to be an input table column."
error_queryExpr_missingAsgnVars t  = error_queryExpr t ++ ",\n the input has to be an expression."
error_queryExpr_notAllInputVars t  = error_queryExpr t ++ ",\n all the inputs have to be input table columns."
error_queryExpr_notAllAsgnVars t   = error_queryExpr t ++ ",\n all the inputs have to be expressions."
error_queryExpr_repeatingVars t    = error_queryExpr t ++ ",\n variables are repeating in different args of the term."

-- internall errors that may come due to bugs in the analyser itself
error_internal      = "INTERNAL ERROR: Some internal analyser problem: "
error_internal_queryExprFilter t       = error_internal ++ "\n query expression " ++ show t ++ "identified as a filter."
error_internal_normRegroup             = error_internal ++ "\n norm regroup problem."
error_internal_extractScaling t        = error_internal ++ "\n cannot extract scaling from " ++ show t
error_internal_sensitivityMatrix n1 n2 = error_internal ++ "\n " ++ show n2 ++ " tables, but " ++ show n1 ++ " columns in sensitivity matrix."
error_internal_fillMissing x i xs      = "case x < i in fillMissing: " ++ show x ++ " < " ++ show i ++ " in " ++ show xs

error_arrElem x xs  = "INTERNAL ERROR: Element " ++ show x ++ " is not in " ++ show xs

-- this message comes only if debug=true, so pleak.io does not need to parse it
warning_verifyNorm  = "WARNING: Could not prove that the db norm is at least as large as the query norm for sensitivity w.r.t. "
