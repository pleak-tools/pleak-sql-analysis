{-# LANGUAGE OverloadedStrings #-}

module Schema (
  checkAndReportErrors,
  parseSchema,
  typeCheckSchema,
  extractChecks,
  extractUniques,
  extractCatalogUpdates
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

import Logging

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
  (catalog, stmts) <- return $
    typeCheckStatements typeCheckFlags catalog stmts
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
    go stmt = case anSrc (getAnnotation stmt) of
      Nothing -> fatal (printf "Expecting only CREATE statements in scheme. Error in %s." fp)
      Just (_, r, c) -> fatal (printf "Expecting only CREATE statements in scheme. Error at %s:%d:%d." fp r c)
      where
        ann = getAnnotation stmt


------------------------------
-- Extract info from schema --
------------------------------

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
  | CreateTable _ _ as cs _ _ _ <- stmt =
      normalize $ mapMaybe goAttr as ++ mapMaybe goConstr cs
  | otherwise = ice "Expecting a CREATE TABLE statement."
  where

    normalize = nub . map sort

    isUniqueRow RowPrimaryKeyConstraint{} = True
    isUniqueRow RowUniqueConstraint{} = True
    isUniqueRow _ = False

    goAttr (AttributeDef _ n _ rcs _)
      | any isUniqueRow rcs = Just [n]
      | otherwise = Nothing

    goConstr (UniqueConstraint _ _ ns) = Just ns
    goConstr (PrimaryKeyConstraint _ _ ns) = Just ns
    goConstr _ = Nothing

-- TODO: it's also possible that table constraints make some more columns NOT NULL
-- This is becayse primary key constraint implies NOT NULL.
-- ^ Extract catalog updates from CREATE TABLE statements.
extractCatalogUpdates :: Statement -> [CatalogUpdate]
extractCatalogUpdates stmt
  | CreateTable _ name as _cs _ _ _ <- stmt = go name as
  | otherwise = ice "Expecting a CREATE TABLE statement."
  where
    isNotNull NotNullConstraint{} = True
    isNotNull RowPrimaryKeyConstraint{} = True
    isNotNull _ = False

    isNull NullConstraint{} = True
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