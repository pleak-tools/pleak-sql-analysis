{-# LANGUAGE OverloadedStrings #-}

import Control.Monad
import Data.List
import Data.Char
import Database.HsSqlPpp.Catalog
import Database.HsSqlPpp.Dialect
import Database.HsSqlPpp.Pretty
import Database.HsSqlPpp.Syntax
import Text.Groom

import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.IO as T

import Catalog
import Logging
import SelectQuery
import Schema
import Z3Bridge
import LocalSensitivity
import ProgramOptions

unitSeparator :: T.Text
unitSeparator = T.pack [chr 31]

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

zipFromOneList [] = []
zipFromOneList (x1 : x2 : xs) = (x1,x2) : zipFromOneList xs

unzipToOneList [] = []
unzipToOneList ((x1,x2) : xs) = x1 : x2 : unzipToOneList xs

-------------------
-- Main function --
-------------------

main :: IO ()
main = do
  args <- getProgramOptions
  let dialect = postgresDialect
  schemaText <- T.readFile (schemaFp args)
  (tableIds, tableNames, stmts) <-
    if alternative args
      then do
        let (tableIds, schemaTexts) = unzip $ zipFromOneList $ T.splitOn unitSeparator schemaText
        let sFp = schemaFp args
        stmtss <- zipWithM (parseSchema dialect) (map ((sFp ++) . ('(' :) . (++ ")") . show) [1..]) schemaTexts
        let tableNamess = map extractTableNames stmtss
        return (tableIds, tableNamess, concat stmtss)
      else do
        stmts <- parseSchema dialect (schemaFp args) schemaText
        --print stmts
        return (undefined, undefined, stmts)
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
  (wholeQuery,queries) <- parseSelectQuery dialect (queryFp args) src
  queries <- do
    query <- typeCheckSelectQuery dialect (local args) False (queryFp args) catalog wholeQuery
    --putStrLn (groom query)
    --T.putStrLn (prettyQueryExpr defaultPrettyFlags query)
    let numqueries = length queries
    forM (zip queries [1..]) $ \ (query,i) -> do
      --putStrLn (groom query)
      query <- typeCheckSelectQuery dialect (local args) True (queryFp args) catalog query
      when (debugPrintQuery args) $ do
        when (numqueries > 1) $ putStrLn $ "Query " ++ show i ++ ":"
        if debugVerbose args
          then putStrLn (groom query)
          else T.putStrLn (prettyQueryExpr defaultPrettyFlags query)
      return query
  --query <- parseSelectQuery dialect (queryFp args) src
  --query <- typeCheckSelectQuery dialect (local args) (queryFp args) catalog query

  --when (debugPrintQuery args) $
  --  if debugVerbose args
  --    then putStrLn (groom query)
  --    else T.putStrLn (prettyQueryExpr defaultPrettyFlags query)

  -- putStrLn $ groomStripped $ extractJoinTables query
  -- forM_ stmts $ \stmt -> do
  --   putStrLn $ show $ extractName stmt
  --   putStrLn $ groomStripped $ extractUniques stmt
  if local args
    then
      forM_ queries $ \ query ->
        performLocalSensitivityAnalysis
                        (debugVerbose args)
                        (dbFromCatalogUpdates catUpdates)
                        query
    else do
      let numqueries = length queries
      ress <- forM (zip queries [1..]) $ \ (query,i) -> do
        res <- performAnalysis args
                               (dbUniqueInfoFromStatements stmts)
                               (dbFromCatalogUpdates catUpdates)
                               query
        unless (alternative args) $ do
          when (numqueries > 1) $ putStrLn $ "Query " ++ show i ++ ":"
          case res of
            Left res -> printAnalysisResults args res
            Right _ -> return ()
        return $ case res of
          Left res -> analysisResultsToInts args res
          Right res -> res
      let res = combineAnalysisResults ress
      if alternative args
        then
          T.putStr $ T.intercalate unitSeparator $ unzipToOneList $ zip tableIds (map (T.pack . show) (alternativeAnalysisResults tableNames res))
        else
          when (sensitivity args == -1 || numqueries > 1 || length res < sum (map (length . fst) ress)) $ printCombinedAnalysisResults res
      when (primaryKeys args) $ do
        ress <- mapM (findPrimaryKeys args
                                      (dbUniqueInfoFromStatements stmts)
                                      (dbFromCatalogUpdates catUpdates))
                     queries
        let res = combinePrimaryKeys wholeQuery ress
        if alternative args
          then
            mapM_ T.putStr [unitSeparator, unitSeparator, T.pack $ map (\ b -> if b then '1' else '0') res]
          else
            forM_ (zip res [1..]) $ \ (b,i) ->
              putStrLn $ "Result column " ++ show i ++ " " ++ (if b then "is" else "is not") ++ " primary key"
