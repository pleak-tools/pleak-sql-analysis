module ProgramOptions
  (ProgramOptions(..), getProgramOptions)
  where

import Options.Applicative
import Data.Semigroup ((<>))

data ProgramOptions
  = ProgramOptions {
    inputFp          :: FilePath,
    alternative      :: Bool,
    generateQueries  :: Bool,
    getEpsilon       :: Double,
    getBeta          :: Maybe Double
  }

programArgs :: Parser ProgramOptions
programArgs = ProgramOptions
  <$> strArgument (metavar "INPUT" <> help "Input file")
  <*> switch (short 'a' <> long "alternative" <> hidden <> help "Use alternative input and output format")
  <*> switch (short 'Q' <> long "queries" <> hidden <> help "Generate SQL queries for computing sensitivity instead of actually computing it")
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
