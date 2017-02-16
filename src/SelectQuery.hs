module SelectQuery (parseSelectQuery, typeCheckSelectQuery) where

import Control.Monad
import Data.Maybe
import Database.HsSqlPpp.Catalog
import Database.HsSqlPpp.Dialect
import Database.HsSqlPpp.Parse
import Database.HsSqlPpp.Syntax
import Database.HsSqlPpp.TypeCheck
import System.Exit

import qualified Data.Text.Lazy as T

import Schema -- TODO: workaround
import Logging

parseSelectQuery :: Dialect -> FilePath -> T.Text -> IO QueryExpr
parseSelectQuery dialect fp src =
  case parseQueryExpr parseFlags fp Nothing src of
    Left err -> fatal (show err)
    Right query@Select{} -> return query
    Right _ -> fatal "Unsupported query type. Expecting basic SELECT query."
  where
    parseFlags = defaultParseFlags { pfDialect = dialect }

unsupportedFeatures :: QueryExpr -> [String]
unsupportedFeatures query =
  ["DISTINCT" | selDistinct query == Distinct] ++
  ["GROUP BY" | not.null $ selGroupBy query] ++
  ["LIMIT"    | isJust $ selLimit query] ++
  ["OFFSET"   | isJust $ selOffset query] ++
  ["HAVING"   | isJust $ selHaving query]

typeCheckSelectQuery :: Dialect -> FilePath -> Catalog -> QueryExpr -> IO QueryExpr
typeCheckSelectQuery dialect fp catalog query = do
  query <- return $ typeCheckQueryExpr typeCheckFlags catalog query
  queryErrs <- checkAndReportErrors query
  when queryErrs exitFailure
  -- Because type checker may rewrite queries to a different form
  -- we perform feature check late.
  let unsupp = unsupportedFeatures query
  forM_ unsupp $ \str ->
    err $ str ++ " clause is not supported"
  when (not $ null unsupp) exitFailure
  return query
  where
    typeCheckFlags = defaultTypeCheckFlags {
      tcfAddQualifiers = True,
      -- tcfAddFullTablerefAliases = True,
      tcfAddSelectItemAliases = True,
      tcfExpandStars = True,
      tcfDialect = dialect
    }