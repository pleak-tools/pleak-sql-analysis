{-# LANGUAGE OverloadedStrings #-}

import Control.Monad
import Data.Data
import Data.Generics.Uniplate.Data
import Data.List
import Data.Maybe
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

ncStrT :: NameComponent -> Text
ncStrT = pack . ncStr

typeNameToCatNameExtra :: TypeName -> CatNameExtra
typeNameToCatNameExtra (SimpleTypeName _ n) = mkCatNameExtra (nameToText n)
typeNameToCatNameExtra _ = ice "Unsupported TypeName."

extractChecks :: Statement -> [ScalarExpr]
extractChecks stmt
  | CreateTable _ _ as cs _ _ _ <- stmt = concatMap goAttr as ++ mapMaybe goConstr cs
  | otherwise = ice "Expecting a CREATE TABLE statement."
  where

    goAttr (AttributeDef _ _ _ rcs _) = mapMaybe goRow rcs

    goRow (RowCheckConstraint _ _ e) = Just e
    goRow _ = Nothing

    goConstr (CheckConstraint _ _ e) = Just e
    goConstr _ = Nothing

extractUniques :: Statement -> [[NameComponent]]
extractUniques stmt
  | CreateTable _ _ as cs _ _ _ <- stmt = mapMaybe goAttr as ++ mapMaybe goConstr cs
  | otherwise = ice "Expecting a CREATE TABLE statement."
  where

    isUniqueRow (RowPrimaryKeyConstraint {}) = True
    isUniqueRow (RowUniqueConstraint {}) = True
    isUniqueRow _ = False

    goAttr (AttributeDef _ n _ rcs _)
      | any isUniqueRow rcs = Just [n]
      | otherwise = Nothing

    goConstr (UniqueConstraint _ _ ns) = Just ns
    goConstr (PrimaryKeyConstraint _ _ ns) = Just ns
    goConstr _ = Nothing

-- TODO: it's also possible that table constraint make column NOT NULL
-- ^ Extract catalog updates from CREATE TABLE statements.
extractCatalogUpdates :: Statement -> [CatalogUpdate]
extractCatalogUpdates stmt
  | CreateTable _ name as _cs _ _ _ <- stmt = go name as
  | otherwise = ice "Expecting a CREATE TABLE statement."
  where
    isNotNull (NotNullConstraint {}) = True
    isNotNull (RowPrimaryKeyConstraint {}) = True
    isNotNull _ = False

    isNull (NullConstraint {}) = True
    isNull _ = False

    go name as = [CatCreateTable ("public", nameToText name)
        [ (pack (ncStr name), catNameExtra) |
          AttributeDef _ name ty rcs _ <- as,
          let notNull = any isNotNull rcs && not (any isNull rcs),
          let catNameExtra = (typeNameToCatNameExtra ty) {
              catNullable = not notNull
            }
        ]
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
  let catUpdates = concatMap extractCatalogUpdates stmts

  -- T.putStrLn (prettyStatements defaultPrettyFlags stmts)

  -- forM_ stmts $ \stmt -> do
  --   putStrLn $ groom $ extractUniques stmt

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
