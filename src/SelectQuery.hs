{-# LANGUAGE LambdaCase #-}

module SelectQuery (
  parseSelectQuery,
  typeCheckSelectQuery,
  extractWhereExpr,
  extractJoinTables)
  where

import Control.Monad
import Database.HsSqlPpp.Annotation
import Database.HsSqlPpp.Catalog
import Database.HsSqlPpp.Dialect
import Database.HsSqlPpp.Parse
import Database.HsSqlPpp.Syntax
import Database.HsSqlPpp.TypeCheck
import Data.Char
import Data.Generics.Uniplate.Data
import Data.IORef
import Data.List
import Data.Maybe
import System.Exit
import Text.Printf

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

type Reason = String
type Loc = Maybe SourcePosition -- using location of hssqlppp

prettyLoc :: String -> Loc -> String
prettyLoc msg Nothing = msg
prettyLoc msg (Just (fp, r, c)) = printf "%s. Error at %s:%d:%d" msg fp r c

unsupportedClauses :: Bool -> QueryExpr -> [Reason]
unsupportedClauses False query =
  ["ALL"      | selDistinct query == All] ++
  ["GROUP BY" | not.null $ selGroupBy query] ++
  ["LIMIT"    | isJust $ selLimit query] ++
  ["OFFSET"   | isJust $ selOffset query] ++
  ["HAVING"   | isJust $ selHaving query]
unsupportedClauses True query =
  ["LIMIT"    | isJust $ selLimit query] ++
  ["OFFSET"   | isJust $ selOffset query] ++
  ["HAVING"   | isJust $ selHaving query]

unsupportedFrom :: QueryExpr -> [(Loc, Reason)]
unsupportedFrom query =
  [(anSrc a, "Subquery")   | SubTref a _ <- trefs] ++
  [(anSrc a, "Function")   | FunTref a _ <- trefs] ++
  [(anSrc a, "???")        | OdbcTableRef a _ <- trefs] ++
  [(anSrc a, showJoin j)   | JoinTref a _ _ j _ _ _ <- trefs, j `notElem` [Inner, Cross]] ++
  [(anSrc a, "Join USING") | JoinTref _ _ _ _ _ _ (Just (JoinUsing a _)) <- trefs] ++ -- TODO: handle these properly
  [(anSrc a, "Full alias") | FullAlias a _ _ _ <- trefs] -- TODO: also handle this properly
  where
    trefs = universeBi query
    showJoin j = headToUpper (map toLower (show j)) ++ " join"
    headToUpper [] = []
    headToUpper (x : xs) = toUpper x : xs

-- ^ Get locations of unsupported expressions.
-- ^ Both from WHERE clause and joins.
-- TODO: Dont descend under already unsupported expressions?
unsupportedWhere :: QueryExpr -> [Loc]
unsupportedWhere query =
  map (anSrc.getAnnotation) $
  filter (not.isSupportedWhereExpr) $
  universeBi (selWhere query) ++ universeBi (selTref query)

isSupportedWhereExpr :: ScalarExpr -> Bool
isSupportedWhereExpr = \case
  NumberLit{}      -> True
  StringLit{}      -> True
  -- NullLit{}     -> True
  BooleanLit{}     -> True
  Identifier{}     -> True
  Parens{}         -> True
  PrefixOp _ n _   -> nameToStr n `elem` ops
  BinaryOp _ n _ _ -> nameToStr n `elem` ops
  _                -> False
  where
    ops = ["=", "<", ">", "<=", ">=", "and", "or", "+", "-", "*", "/"]

nameToStr :: Name -> String
nameToStr (Name _ ns) = intercalate "." (map ncStr ns)
nameToStr AntiName{} = ice "Unexpected AntiName."

extractWhereExpr :: QueryExpr -> [ScalarExpr]
extractWhereExpr query =
  maybeToList (selWhere query) ++
  [e | JoinTref a _ _ _ _ _ (Just (JoinOn _ e)) <- universeBi query]

extractJoinTables :: QueryExpr -> [TableRef]
extractJoinTables = concatMap go . selTref
  where
    go (JoinTref _ l _ _ _ r _) = go l ++ go r
    go t = [t]

typeCheckSelectQuery :: Dialect -> Bool -> FilePath -> Catalog -> QueryExpr -> IO QueryExpr
typeCheckSelectQuery dialect local fp catalog query = do
  query <- return $ typeCheckQueryExpr typeCheckFlags catalog query
  queryErrs <- checkAndReportErrors query
  when queryErrs exitFailure -- dont bail?
  -- Because type checker may rewrite queries to a different form
  -- we perform feature check late.
  bailRef <- newIORef False
  forM_ (unsupportedClauses local query) $ \str -> do
    bailRef `writeIORef` True
    err $ str ++ " clause is not supported"
  forM_ (unsupportedFrom query) $ \ (loc, str) -> do
    bailRef `writeIORef` True
    err $ prettyLoc (printf "%s not supported in FROM clause." str) loc
  forM_ (unsupportedWhere query) $ \loc -> do
    bailRef `writeIORef` True
    err $ prettyLoc "Unsupported expression in WHERE clause or join." loc
  bail <- readIORef bailRef
  when bail exitFailure
  return query
  where
    typeCheckFlags = defaultTypeCheckFlags {
      tcfAddQualifiers = True,
      -- tcfAddFullTablerefAliases = True,
      tcfAddSelectItemAliases = True,
      tcfExpandStars = True,
      tcfDialect = dialect
    }
