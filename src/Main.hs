{-# LANGUAGE OverloadedStrings #-}

import Control.Monad
import Data.List
import Database.HsSqlPpp.Catalog
import Database.HsSqlPpp.Dialect
import Database.HsSqlPpp.Pretty
import Database.HsSqlPpp.Syntax
import Text.Groom

import qualified Data.Text.Lazy.IO as T

import Catalog
import Logging
import SelectQuery
import Schema
import Z3Bridge
import LocalSensitivity
import ProgramOptions

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

-------------------
-- Main function --
-------------------

main :: IO ()
main = do
  args <- getProgramOptions
  let dialect = postgresDialect
  schemaText <- T.readFile (schemaFp args)
  stmts <- parseSchema dialect (schemaFp args) schemaText
  (catalog, stmts) <- typeCheckSchema dialect (schemaFp args) catalog stmts
  let catUpdates = concatMap extractCatalogUpdates stmts

  -- T.putStrLn (prettyStatements defaultPrettyFlags stmts)

  -- forM_ stmts $ \stmt -> do
  --   putStrLn $ groom $ extractUniques stmt

  when (debugPrintSchema args) $
    mapM_ (putStrLn . groom) catUpdates

  catalog <- case updateCatalog catUpdates catalog of
    Left e -> fatal $ show e
    Right c -> return c

  -- putStrLn (groom stmts')
  -- T.putStrLn (prettyStatements defaultPrettyFlags stmts')

  src <- T.readFile (queryFp args)
  query <- parseSelectQuery dialect (queryFp args) src
  query <- typeCheckSelectQuery dialect (queryFp args) catalog query

  when (debugPrintQuery args) $
    if debugVerbose args
      then putStrLn (groom query)
      else T.putStrLn (prettyQueryExpr defaultPrettyFlags query)
  -- putStrLn $ groomStripped $ extractJoinTables query
  -- forM_ stmts $ \stmt -> do
  --   putStrLn $ show $ extractName stmt
  --   putStrLn $ groomStripped $ extractUniques stmt
  if local args
    then
      performLocalSensitivityAnalysis
                      (dbFromCatalogUpdates catUpdates)
                      query
    else
      performAnalysis args
                      (dbUniqueInfoFromStatements stmts)
                      (dbFromCatalogUpdates catUpdates)
                      query
