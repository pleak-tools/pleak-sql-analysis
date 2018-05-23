{-# LANGUAGE OverloadedStrings #-}

module SchemaQ (
  checkAndReportErrors,
  parseSchemas,
  parseSchema,
  extractTypes,
  typeCheckSchema
  ) where

import Control.Monad
import Data.Data
import Data.Generics.Uniplate.Data
import Data.List
import Data.Maybe
import Data.Text (Text, pack)
import Database.HsSqlPpp.Annotation
import Database.HsSqlPpp.Catalog
import Database.HsSqlPpp.Dialect
import Database.HsSqlPpp.Parse
import Database.HsSqlPpp.Syntax
import Database.HsSqlPpp.TypeCheck
import Text.Printf
import System.Exit

import qualified Data.Text.Lazy as T

import LoggingQ

-- TODO: move elsewhere
-- ^ Report all type errors and return True if any were found.
-- Does so by extracting every field of type "Annotation"
checkAndReportErrors :: Data a => a -> IO Bool
checkAndReportErrors x = do
  let errorAnns = filter (not . null . anErrs) $ universeBi x
  forM_ errorAnns $ \a -> do
    case anSrc a of
      Nothing -> err "Type error"
      Just (fp, r, c) -> err $ printf "Type error at %s:%d:%d" fp r c
    mapM_ (err . ("  " ++) . show) $ anErrs a
  return $ not $ null errorAnns

-------------------------------
-- Parsing and type checking --
-------------------------------
parseSchemas :: String -> IO [Statement]
parseSchemas s =
  let dialect = postgresDialect in
  let src = T.pack s in
  parseSchema dialect "errorlog.txt" src

parseSchema :: Dialect -> FilePath -> T.Text -> IO [Statement]
parseSchema dialect fp src =
  case parseStatements parseFlags fp Nothing src of
    Left e -> fatal $ show e
    Right stmts -> return stmts
  where
    parseFlags = defaultParseFlags { pfDialect = dialect }

typeCheckSchema :: Dialect -> FilePath -> Catalog -> [Statement] -> IO (Catalog, [Statement])
typeCheckSchema dialect fp catalog stmts = do
  verifySchema fp stmts
  (catalog, stmts) <- return $ typeCheckStatements typeCheckFlags catalog stmts
  anyErrors <- checkAndReportErrors stmts
  when anyErrors exitFailure
  return (catalog, stmts)
  where
    typeCheckFlags = defaultTypeCheckFlags {
      tcfAddQualifiers = True,
      -- tcfAddFullTablerefAliases = True,
      tcfAddSelectItemAliases = True,
      tcfExpandStars = True,
      tcfDialect = dialect
    }

-- Verify that given statements all create tables.
verifySchema :: FilePath -> [Statement] -> IO ()
verifySchema fp = mapM_ go
  where
    go CreateTable{} = return ()
    go CreateFunction{} = return ()
    go stmt = case anSrc (getAnnotation stmt) of
      Nothing -> fatal (printf "Expecting only CREATE statements in schema. Error in %s." fp)
      Just (fp, r, c) -> fatal (printf "Expecting only CREATE statements in schema. Error at %s:%d:%d." fp r c)
      --Just (_, r, c) -> fatal (printf "Expecting only CREATE statements in schema. Error at %s:%d:%d." fp r c)

extractTypes :: Statement -> [(String,String)]
extractTypes (CreateTable _ (Name _ [Nmc tableName]) attributeDefList _ _ _) =
    let attrTypes = extractTypesRec attributeDefList in
    map (\(x, y) -> (tableName ++ "." ++ x, y)) attrTypes

extractTypesRec :: [AttributeDef] -> [(String,String)]
extractTypesRec [] = []
extractTypesRec ((AttributeDef _ (Nmc colName) (SimpleTypeName _ (Name _ [Nmc typeName])) _ _) : xs) =
    (colName,typeName) : (extractTypesRec xs)


