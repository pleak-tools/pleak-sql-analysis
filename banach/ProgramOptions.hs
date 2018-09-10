module ProgramOptions
  (ProgramOptions(..), getProgramOptions)
  where

import Options.Applicative
import Data.Semigroup ((<>))

data ProgramOptions
  = ProgramOptions {
    inputFp1         :: FilePath,
    inputFp2         :: FilePath,
    inputFp3         :: FilePath,
    alternative      :: Bool,
    policyAnalysis   :: Bool,
    generateQueries  :: Bool,
    dbSensitivity    :: Bool,
    dbCreateTables   :: Bool,
    dbConnString     :: String,
    delimiter        :: String,
    getEpsilon       :: Double,
    getBeta          :: Maybe Double
  }

programArgs :: Parser ProgramOptions
programArgs = ProgramOptions
  <$> strArgument (metavar "SCHEMA INPUT" <> help "schema input file")
  <*> strArgument (metavar "QUERY INPUT" <> help "query input file")
  <*> strArgument (metavar "ATTACKER INPUT" <> help "attacker description input file")
  <*> switch (short 'a' <> long "alternative" <> hidden <> help "Use alternative input and output format")
  <*> switch (short 'p' <> long "policy-analysis" <> hidden <> help "Analyse privacy treating epsilon in [0,1] as attacker's guessing probability")
  <*> switch (short 'Q' <> long "queries" <> hidden <> help "Generate SQL queries for computing sensitivity instead of actually computing it")
  <*> switch (short 'D' <> long "db-sensitivity" <> hidden <> help "Send the generated query for computing sensitivity automatically to the database")
  <*> switch (long "db-create-tables" <> hidden <> help "Create the required tables in the database using the data in input files")
  <*> strOption (short 'C' <> long "db-connection" <> value "dbname=banach" <> help "Specify database connection string")
  <*> strOption (short 'd' <> long "delimiter" <> value " " <> help "Specify data .csv file delimiter (by default a whitespace)")
  <*> option auto (short 'e' <> long "epsilon" <> value 1.0 <> help "Specify epsilon (default is 1)")
  <*> optional (option auto (short 'B' <> long "beta" <> help "Specify beta (default is to choose automatically)"))

getProgramOptions :: IO ProgramOptions
getProgramOptions = execParser opts
  where
    opts = info (programArgs <**> helper)
      (fullDesc
      <> progDesc "Performs static analysis of the file INPUT that contains the query\
                  \ and the name of the file containing the database."
      <> header "banach - smooth derivative sensitivity analyzer for Banach spaces")
