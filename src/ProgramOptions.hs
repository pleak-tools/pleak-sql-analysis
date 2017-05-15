module ProgramOptions
  (ProgramOptions(..), getProgramOptions)
  where

import Options.Applicative

data ProgramOptions
  = ProgramOptions {
    schemaFp          :: FilePath,
    queryFp           :: FilePath,
    sensitivity       :: Int,
    z3Path            :: Maybe FilePath,
    local             :: Bool,
    alternative       :: Bool,
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
  <*> option auto (short 's' <> long "sensitivity" <> metavar "INT" <> value 1 <>
        help "Specify sensitivity to check (default is 1)")
  <*> maybeStrOption (long "z3-path" <> metavar "PATH" <> help "Z3 path.")
  <*> switch (short 'l' <> long "local" <> help "Use local sensitivity analysis")
  <*> switch (short 'a' <> long "alternative" <> hidden <> help "Use alternative input and output format")
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

