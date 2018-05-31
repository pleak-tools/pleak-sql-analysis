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
    primaryKeys       :: Bool,
    direct            :: Bool,
    dbConnString      :: String,
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
  <*> switch (short 'p' <> long "primary-keys" <> hidden <> help "Find which columns of the result table are primary keys")
  <*> switch (short 'D' <> long "direct" <> hidden <> help "Analyze tables used more than once directly instead of each copy separately (EXPERIMENTAL)")
  <*> strOption (short 'C' <> long "db-connection" <> value "dbname=banach" <> help "Specify database connection string")
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

