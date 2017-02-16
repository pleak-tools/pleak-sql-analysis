module SelectQuery (parseSelectQuery, typeCheckSelectQuery) where

import Control.Monad (when)
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
    Right query@(Select { }) -> return query
    Right _ -> fatal "Unsupported query type. Expecting basic SELECT query."
  where
    parseFlags = defaultParseFlags { pfDialect = dialect }

typeCheckSelectQuery :: Dialect -> FilePath -> Catalog -> QueryExpr -> IO QueryExpr
typeCheckSelectQuery dialect fp catalog query = do
  query <- return $ typeCheckQueryExpr typeCheckFlags catalog query
  queryErrs <- checkAndReportErrors query
  when queryErrs exitFailure
  return query
  where
    typeCheckFlags = defaultTypeCheckFlags {
      tcfAddQualifiers = True,
      -- tcfAddFullTablerefAliases = True,
      tcfAddSelectItemAliases = True,
      tcfExpandStars = True,
      tcfDialect = dialect
    }