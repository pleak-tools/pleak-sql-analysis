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
    inputFp4         :: FilePath,
    inputFp5         :: FilePath,
    alternative      :: Bool,
    combinedSens     :: Bool,
    timeSeries       :: Maybe String,
    maxProvTimepoints:: Int,
    policyAnalysis   :: Bool,
    generateQueries  :: Bool,
    dbSensitivity    :: Bool,
    dbCreateTables   :: Bool,
    dbConnString     :: String,
    delimiter        :: String,
    getSigmoidBeta   :: Double,
    getSigmoidPrecision :: Double,
    getEpsilon       :: Double,
    getBeta          :: Maybe Double,
    getG             :: Maybe Double,
    numOfQueries     :: Int,
    errorUBprob      :: Double,
    psqlDateStyle    :: String,
    getDelta         :: Double
  }

programArgs :: Parser ProgramOptions
programArgs = ProgramOptions
  <$> strArgument (metavar "SCHEMA INPUT" <> help "schema input file")
  <*> strArgument (metavar "QUERY INPUT" <> help "query input file")
  <*> strArgument (metavar "ATTACKER INPUT" <> help "attacker description input file")
  <*> strOption (long "policy" <> value "" <> help "policy description input file (used only by policy analyser)")
  <*> strOption (long "localsenspath" <> value "" <> help "path to the local sensitivity analyser (used only with -c parameter)")
  <*> switch (short 'a' <> long "alternative" <> hidden <> help "Use alternative input and output format")
  <*> switch (short 'c' <> long "combined-sens" <> hidden <> help "Call local sensitivity analyzer (must be at ./sqlsa) and combine the results of the two analyzers")
  <*> optional (strOption (short 't' <> long "time-series" <> metavar "TABLE.COL" <> hidden <> help "Analyse time series using TABLE.COL as the time column (comma-separated list of time columns in multiple tables can be used)"))
  <*> option auto (short 'm' <> long "max-prov-timepoints" <> value 1 <> help "Specify the maximum number of time points where a provenance (or row) can affect the query change, including the time points when it is joined with other rows (default is 1)")
  <*> switch (short 'p' <> long "policy-analysis" <> hidden <> help "Analyse privacy treating epsilon in [0,1] as attacker's guessing probability")
  <*> switch (short 'Q' <> long "queries" <> hidden <> help "Generate SQL queries for computing sensitivity instead of actually computing it")
  <*> switch (short 'D' <> long "db-sensitivity" <> hidden <> help "Send the generated query for computing sensitivity automatically to the database")
  <*> switch (long "db-create-tables" <> hidden <> help "Create the required tables in the database using the data in input files")
  <*> strOption (short 'C' <> long "db-connection" <> value "dbname=banach" <> help "Specify database connection string")
  <*> strOption (short 'd' <> long "delimiter" <> value " " <> help "Specify data .csv file delimiter (by default a whitespace)")
  <*> option auto (long "sigmoid-beta" <> value 1e-100 <> help "Specify the smoothness beta of sigmoids and tauoids (default is 1e-100)")
  <*> option auto (long "sigmoid-precision" <> value 5.0 <> help "Specify the precision of sigmoids and tauoids (default is 5.0)")
  <*> option auto (short 'e' <> long "epsilon" <> value 1.0 <> help "Specify epsilon (default is 1)")
  <*> optional (option auto (short 'B' <> long "beta" <> help "Specify beta (default is to choose automatically)"))
  <*> optional (option auto (short 'G' <> long "distance-G" <> help "Specify G (the distance between two databases that differ by exactly one row)"))
  <*> option auto (short 'n' <> long "numOfQueries" <> value 1 <> help "Specify the limit on the number of queries applied to the same data (default is 1)")
  <*> option auto (long "errorUB" <> value 0.78055 <> help "Specify the probability with which the noise fits below noise magnitude")
  <*> strOption (long "datestyle" <> value "European" <> help "Specify the psql datestyle (default is 'European')")
  <*> option auto (long "delta" <> value (2**(-40)) <> help "Specify the delta for (epsilon,delta)-DP (used only for Lapalce noise and only in DS/CS analysis)")

getProgramOptions :: IO ProgramOptions
getProgramOptions = execParser opts
  where
    opts = info (programArgs <**> helper)
      (fullDesc
      <> progDesc "Performs static analysis of the file INPUT that contains the query\
                  \ and the name of the file containing the database."
      <> header "banach - smooth derivative sensitivity analyzer for Banach spaces")
