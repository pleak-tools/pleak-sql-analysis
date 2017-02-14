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
import System.Environment
import System.Exit
import System.IO
import Text.Groom
import Text.Printf

import qualified Data.Text.Lazy.IO as T

import Catalog

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

main :: IO ()
main = do
  args <- getArgs
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
  case args of
    [schemaFile, queryFile] -> do
      schemaText <- T.readFile schemaFile
      stmts <- case parseStatements parseFlags schemaFile Nothing schemaText of
        Left err -> fatal (show err)
        Right stmts -> return stmts

      verifySchema schemaFile stmts
      let (catalog', stmts') = typeCheckStatements typeCheckFlags catalog stmts
      stmtErrs <- checkAndReportErrors stmts'
      when stmtErrs exitFailure
      putStrLn (groom stmts')
      -- T.putStrLn (prettyStatements defaultPrettyFlags stmts')

      src <- T.readFile queryFile
      query <- case parseQueryExpr parseFlags queryFile Nothing src of
        Left err -> fatal (show err)
        Right query@(Select { }) -> return query
        Right _ -> fatal "Unsupported query type. Expecting basic SELECT query."

      mapM_ (putStrLn . groom) $ deconstructCatalog catalog'
      let query' = typeCheckQueryExpr typeCheckFlags catalog' query
      queryErrs <- checkAndReportErrors query'
      when queryErrs exitFailure

      -- T.putStrLn (prettyQueryExpr defaultPrettyFlags query')
      putStrLn (groom query')
    _ -> die "Invalid program arguments. Expecting a two files of which first contains schema and second the SQL query to analyze."
