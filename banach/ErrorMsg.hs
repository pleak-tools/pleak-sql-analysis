module ErrorMsg where

--------------------------------------------------------
-- some hardcoded error message

error_parseSqlQuery = "ERROR: Could not parse the query from file "
error_parseQuery    = "ERROR: Could not parse the query from file "
error_parseNorm     = "ERROR: Could not parse the norm from file "
error_parseData     = "ERROR: Could not parse the data table from file "

error_queryExpr     = "ERROR: Unsupported term in the expression "
error_filterExpr    = "ERROR: Unsupported filter "

error_internal      = "INTERNAL ERROR: Some internal analyser problem: "

warning_verifyNorm  = "WARNING: Could not prove that the db norm is at least as large as the query norm for sensitivity w.r.t. "
