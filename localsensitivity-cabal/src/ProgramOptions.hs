module ProgramOptions
  (ProgramOptions(..), getProgramOptions)
  where

import Options.Applicative
import Data.Semigroup ((<>))

data ProgramOptions
  = ProgramOptions {
    schemaFp          :: FilePath,
    queryFp           :: FilePath,
    sensitivity       :: Int,
    z3Path            :: Maybe FilePath,
    local             :: Bool,
    alternative       :: Bool,
    combinedSens      :: Bool,
    localSens         :: Bool,
    countQuery        :: Bool,
    primaryKeys       :: Bool,
    direct            :: Bool,
    dbConnString      :: String,
    forbidden         :: String,
    tableGs           :: String,
    getG              :: Double,
    getBeta           :: Maybe Double,
    getSumExprBound   :: Double,
    printQuantiles    :: Bool,
    debugPrintZ3      :: Bool,
    debugPrintSchema  :: Bool,
    debugPrintQuery   :: Bool,
    debugVerbose      :: Bool
  }

maybeStrOption :: Mod OptionFields String -> Parser (Maybe String)
maybeStrOption mod = Just <$> strOption mod <|> pure Nothing

programArgs :: Parser ProgramOptions
programArgs = ProgramOptions
  <$> strArgument (metavar "SCHEMA" <> help "File containing database schema")
  <*> strArgument (metavar "QUERY" <> help "File containing SQL query")
  <*> option auto (short 's' <> long "sensitivity" <> hidden <> metavar "INT" <> value 1 <>
        help "Specify sensitivity to check (default is 1)")
  <*> maybeStrOption (long "z3-path" <> hidden <> metavar "PATH" <> help "Z3 path.")
  <*> switch (short 'l' <> long "local" <> hidden <> help "Use local sensitivity analysis")
  <*> switch (short 'a' <> long "alternative" <> hidden <> help "Use alternative input and output format")
  <*> switch (short 'c' <> long "combined-sens" <> hidden <> help "Used for calling from the Banach analyzer, creates a temporary file used for combining the results of the two analyzers")
  <*> switch (long "localsens" <> hidden <> help "Estimate an upper bound on local sensitivity from the derivative sensitivity")
  <*> switch (long "count-query" <> hidden <> help "Used for calling from the Banach analyzer, compute the sensitivity of the count query corresponding to the current query")
  <*> switch (short 'p' <> long "primary-keys" <> hidden <> help "Find which columns of the result table are primary keys")
  <*> switch (short 'D' <> long "direct" <> hidden <> help "Analyze tables used more than once directly instead of each copy separately (EXPERIMENTAL)")
  <*> strOption (short 'C' <> long "db-connection" <> value "dbname=banach" <> help "Specify database connection string")
  <*> strOption (short 'f' <> long "forbidden" <> value "" <> hidden <> help "Specify a comma-separated list of forbidden columns (of the form table.column), the analyzer output must not depend on the values in these columns")
  <*> strOption (long "table-Gs" <> value "" <> hidden <> help "Specify a comma-separated list of table G's (of the form table:G), the cost of changing the table by one row")
  <*> option auto (short 'G' <> long "distance-G" <> value 1 <> help "Specify default G (the distance between two databases that differ by exactly one row)")
  <*> optional (option auto (short 'B' <> long "beta" <> hidden <> help "Specify beta (default is to choose automatically)"))
  <*> option auto (short 'S' <> long "sum-expr-bound" <> value 1000 <> hidden <> help "Specify the global upper bound on the absolute value of the function applied to each row")
  <*> switch (long "print-quantiles" <> hidden <> help "Print quantiles of noise distributions")
  <*> switch (long "debug-print-z3" <> hidden <> help "Print generated Z3 input")
  <*> switch (long "debug-print-schema" <> hidden <> help "Print debug information about the database schema")
  <*> switch (long "debug-print-query" <> hidden <> help "Print debug information about the SQL select query")
  <*> switch (long "debug-verbose" <> hidden <> help "More informative but uglier debug output")


getProgramOptions :: IO ProgramOptions
getProgramOptions = execParser opts
  where
    opts = info (programArgs <**> helper)
      (fullDesc
      <> progDesc "Performs static analysis of a SQL QUERY.\
                  \ Database schema is described by SCHEMA."
      <> header "sqla - static SQL sensitivily analyzer")

