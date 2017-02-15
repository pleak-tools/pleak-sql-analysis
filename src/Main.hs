{-# LANGUAGE OverloadedStrings #-}

import Control.Monad
import Data.Data
import Data.Generics.Uniplate.Data
import Data.List
import Database.HsSqlPpp.Annotation
import Database.HsSqlPpp.Catalog
import Database.HsSqlPpp.Dialect
import Database.HsSqlPpp.Parse
import Database.HsSqlPpp.Pretty
import Database.HsSqlPpp.Syntax
import Database.HsSqlPpp.TypeCheck
import GHC.Stack (HasCallStack, withFrozenCallStack)
import Options.Applicative
import System.Environment
import System.Exit
import System.IO
import Text.Groom
import Text.Printf

import qualified Data.Text.Lazy.IO as T
import Data.Text (Text, pack)

import Catalog

---------------------
-- Program options --
---------------------

data ProgramArgs
  = ProgramArgs {
    schemaFp          :: FilePath,
    queryFp           :: FilePath,
    debugPrintSchema  :: Bool,
    debugPrintQuery   :: Bool
  }

programArgs :: Parser ProgramArgs
programArgs = ProgramArgs
  <$> strArgument (metavar "SCHEMA" <> help "File containing database schema")
  <*> strArgument (metavar "QUERY" <> help "File containing SQL query")
  <*> switch (long "debug-print-schema" <> hidden <> help "Print debug information about the database schema")
  <*> switch (long "debug-print-query" <> hidden <> help "Print debug information about the SQL select query")

---------------------------------------------------
-- Some dumb code to pretty print hssqlppp stuff --
---------------------------------------------------

groomStripped :: Show a => a -> String
groomStripped = groomString . stripAnnotations . show

-- Super slow, but whatever
stripAnnotations :: String -> String
stripAnnotations [] = []
stripAnnotations str@(c : cs)
  | "Annotation" `isPrefixOf` str = "_ " ++ go 0 (drop 10 str)
  | otherwise = c : stripAnnotations cs
  where
   go _ [] = []
   go n ('{' : cs) = go (n + 1) cs
   go n ('}' : cs)
     | n == 1 = stripAnnotations cs
     | otherwise = go (n - 1) cs
   go n (c : cs)
     | n == 0 = c : go n cs
     | otherwise = go n cs

------------------------------------
-- Text colors (for ANSI console) --
------------------------------------

red :: String -> String
red s = "\x1b[31m" ++ s ++ "\x1b[0m"

yellow :: String -> String
yellow s = "\x1b[33m" ++ s ++ "\x1b[0m"

green :: String -> String
green s = "\x1b[32m" ++ s ++ "\x1b[0m"

fatal :: String -> IO a
fatal msg = die $ red $ "[FATAL] " ++ msg

err :: String -> IO ()
err msg = hPutStrLn stderr $ red $ "[ERROR] " ++ msg

ice :: HasCallStack => String -> a
ice msg = withFrozenCallStack error $ red $ "[ICE] " ++ msg

-------------------
-- Verify schema --
-------------------

-- Verify that given statements all create tables.
verifySchema :: FilePath -> [Statement] -> IO ()
verifySchema fp = mapM_ go
  where

    go (CreateTable { }) = return ()
    go stmt = case anSrc (getAnnotation stmt) of
      Nothing -> fatal (printf "Expecting only CREATE statements in scheme. Error in %s." fp)
      Just (_, r, c) -> fatal (printf "Expecting only CREATE statements in scheme. Error at %s:%d:%d." fp r c)
      where
        ann = getAnnotation stmt

------------------------------------
-- Extract info from CREATE TABLE --
------------------------------------

nameToText :: Name -> Text
nameToText (AntiName _) = ice "AntiName."
nameToText (Name _ []) = ice "Empty name."
nameToText (Name _ ns) = pack $ go ns
  where
    go [nc] = ncStr nc
    go (nc : ncs) = ncStr nc ++ "." ++ go ncs

typeNameToCatNameExtra :: TypeName -> CatNameExtra
typeNameToCatNameExtra (SimpleTypeName _ n) = mkCatNameExtra (nameToText n)
typeNameToCatNameExtra _ = ice "Unsupported TypeName."

-- TODO: constraints are just ignored. extract them as well
-- TODO: handle not-null!
extractCatalogUpdates :: [Statement] -> [CatalogUpdate]
extractCatalogUpdates stmts = concat [go name as | CreateTable _ name as _cs _ _ _ <- stmts]
  where
    go name as = [CatCreateTable ("public", nameToText name) [
        (pack (ncStr name), typeNameToCatNameExtra ty) | AttributeDef _ name ty _expr _rcs <- as]
      ]

-- ^ Report all type errors and return True if any were found.
-- Does so by extracting every field of type "Annotation"
checkAndReportErrors :: Data a => a -> IO Bool
checkAndReportErrors x = do
  let errorAnns = filter (not . null . anErrs) $ universeBi x
  forM_ errorAnns $ \ann -> do
    case anSrc ann of
      Nothing -> return ()
      Just (fp, r, c) -> err $ printf "Type error at %s:%d:%d" fp r c
    mapM_ (err . ("  " ++) . show) $ anErrs ann
  return $ not $ null errorAnns

-------------------
-- Main function --
-------------------

main :: IO ()
main = do
  args <- execParser opts
  let
    dialect = postgresDialect
    parseFlags = defaultParseFlags { pfDialect = dialect }
    typeCheckFlags = defaultTypeCheckFlags {
      tcfAddQualifiers = True,
      -- tcfAddFullTablerefAliases = True,
      tcfAddSelectItemAliases = True,
      tcfExpandStars = True,
      tcfDialect = dialect
    }

  schemaText <- T.readFile (schemaFp args)
  stmts <- case parseStatements parseFlags (schemaFp args) Nothing schemaText of
    Left err -> fatal (show err)
    Right stmts -> return stmts

  verifySchema (schemaFp args) stmts
  (catalog, stmts) <- return $ -- very much intentional for overshadowing
    typeCheckStatements typeCheckFlags catalog stmts
  stmtErrs <- checkAndReportErrors stmts
  when stmtErrs exitFailure
  let catUpdates = extractCatalogUpdates stmts

  when (debugPrintSchema args) $
    mapM_ (putStrLn . groom) $ catUpdates

  catalog <- case updateCatalog catUpdates catalog of
    Left e -> fatal $ show e
    Right c -> return c

  -- putStrLn (groom stmts')
  -- T.putStrLn (prettyStatements defaultPrettyFlags stmts')

  src <- T.readFile (queryFp args)
  query <- case parseQueryExpr parseFlags (queryFp args) Nothing src of
    Left err -> fatal (show err)
    Right query@(Select { }) -> return query
    Right _ -> fatal "Unsupported query type. Expecting basic SELECT query."

  let query' = typeCheckQueryExpr typeCheckFlags catalog query
  queryErrs <- checkAndReportErrors query'
  when queryErrs exitFailure

  when (debugPrintQuery args) $
    T.putStrLn (prettyQueryExpr defaultPrettyFlags query')
    -- putStrLn (groom query')
  where
    opts = info (programArgs <**> helper)
      (fullDesc
      <> progDesc "Performs static analysis of a SQL QUERY.\
                  \ Database schema is described by SCHEMA."
      <> header "sqla - static SQL sensitivily analyzer")
