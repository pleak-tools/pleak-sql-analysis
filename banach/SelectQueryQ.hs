{-# LANGUAGE LambdaCase #-}

module SelectQueryQ (
  parseQuery,
  parseNamedQuery,
  parseSelectQuery,
  typeCheckSelectQuery,
  combinePrimaryKeys,
  extractSelect,
  extractTrefs,
  extractWhereExpr,
  extractWhere,
  extractJoinTables,
  isSupportedAggregOp)
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

import SchemaQ -- TODO: workaround
import LoggingQ

import ExprQ
import AexprQ
import QueryQ
import ErrorMsg

--parseSelectQuery :: Dialect -> FilePath -> T.Text -> IO QueryExpr
--parseSelectQuery dialect fp src =
--  case parseQueryExpr parseFlags fp Nothing src of
--    Left err -> fatal (show err)
--    Right query@Select{} -> return query
--    Right _ -> fatal "Unsupported query type. Expecting basic SELECT query."
--  where
--    parseFlags = defaultParseFlags { pfDialect = dialect }

parseNamedQuery :: String -> IO [(String, QueryExpr)]
parseNamedQuery s = do
    xs <- parseSchemas s
    return $ map (\(Insert _ (Name _ [Nmc name]) _ query _) -> (name, query)) xs

parseQuery :: String -> IO (QueryExpr, [QueryExpr])
parseQuery s =
  let dialect = postgresDialect in
  let src = T.pack s in
  parseSelectQuery dialect "errorlog.txt" src

parseSelectQuery :: Dialect -> FilePath -> T.Text -> IO (QueryExpr, [QueryExpr])
parseSelectQuery dialect fp src =
  case parseQueryExpr parseFlags fp Nothing src of
    Left err -> fatal (show err)
    Right query -> do
      qs <- extractQueries query
      return (query, qs)
  where
    parseFlags = defaultParseFlags { pfDialect = dialect }
    extractQueries query@Select{} = return [query]
    extractQueries (CombineQueryExpr _ cqt q1 q2) | cqt `elem` [Intersect,Union,Except] = do
      qs1 <- extractQueries q1
      qs2 <- extractQueries q2
      return (qs1 ++ qs2)
    extractQueries _ = fatal "Unsupported query type. Expecting basic SELECT query."

combinePrimaryKeys :: QueryExpr -> [[Bool]] -> [Bool]
combinePrimaryKeys q pks = fst $ f q pks
  where
    f Select{} (pk:pks) = (pk,pks)
    f (CombineQueryExpr _ cqt q1 q2) pks =
      let
        (pk1,pks') = f q1 pks
        (pk2,pks'') = f q2 pks'
        pk =
          case cqt of
            Intersect -> zipWith (||) pk1 pk2
            Union -> map (const False) pk1
            Except -> pk1
      in
        (pk,pks'')

type Reason = String
type Loc = Maybe SourcePosition -- using location of hssqlppp

prettyLoc :: String -> Loc -> String
prettyLoc msg Nothing = msg
prettyLoc msg (Just (fp, r, c)) = printf "%s. Error at %s:%d:%d" msg fp r c

unsupportedClauses :: Bool -> QueryExpr -> [Reason]
unsupportedClauses False query =
--  ["ALL with non-aggregating expressions and without GROUP BY"
--    | selDistinct query == All && not (isSelectListOnlyAggregExprs (selSelectList query)) && null (selGroupBy query) ] ++
  ["LIMIT"    | isJust $ selLimit query] ++
  ["OFFSET"   | isJust $ selOffset query] ++
  ["HAVING"   | isJust $ selHaving query]
unsupportedClauses True query =
  ["LIMIT"    | isJust $ selLimit query] ++
  ["OFFSET"   | isJust $ selOffset query] ++
  ["HAVING"   | isJust $ selHaving query]

unsupportedFrom :: Bool -> QueryExpr -> [(Loc, Reason)]
unsupportedFrom local query =
  [(anSrc a, "Subquery")   | not local, SubTref a _ <- trefs] ++
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
unsupportedWhere :: Bool -> QueryExpr -> [Loc]
unsupportedWhere local query =
  map (anSrc.getAnnotation) $
  filter (not.isSupportedWhereExpr) $
  if local
    then universeBi (selWhere query)
    else universeBi (selWhere query) ++ universeBi (selTref query)

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
  SpecialOp _ n _  -> nameToStr n == "between"
  _                -> False
  where
    ops = ["=", "<", ">", "<=", ">=", "and", "or", "+", "-", "*", "/", "%", "not"]

isSupportedAggregOp :: Name -> Bool
isSupportedAggregOp op = nameToStr op `elem` ["count", "sum", "avg", "min", "max"]

nameToStr :: Name -> String
nameToStr (Name _ ns) = intercalate "." (map ncStr ns)
nameToStr AntiName{} = ice "Unexpected AntiName."

extractSelect :: QueryExpr -> String -> [Function]
extractSelect query y =
    let (SelectList _ xs) = selSelectList query in 
    let ys = if length xs == 1 then [y] else map (\i -> y ++ "~" ++ show i) [0..length xs - 1] in
    zipWith extractTableExpr xs ys

extractTableExpr :: SelectItem -> String -> Function
extractTableExpr (SelExp _ (App _ (Name _ [Nmc aggrOp]) [expr])) y =
    let arg = extractScalarExpr expr in
    case aggrOp of
        "count" -> F arg (SelectCount y)
        "sum"   -> F arg (SelectSum y)
        "min"   -> F arg (SelectMin y)
        "max"   -> F arg (SelectMax y)
        _       -> error $ error_queryExpr_aggrFinal aggrOp

extractTableExpr q _ = error $ error_queryExpr q

extractTrefs :: QueryExpr -> [(String, String)]
extractTrefs query = extractTrefsRec (selTref query)

extractTrefsRec :: [TableRef] -> [(String, String)]
extractTrefsRec [] = []
extractTrefsRec ((TableAlias _ (Nmc tableAlias) (Tref _ (Name _ [Nmc tableName]))):ts) =
    (tableName,tableAlias) : extractTrefsRec ts
extractTrefsRec (Tref _ (Name _ [Nmc tableName]):ts) =
    (tableName,tableName) : extractTrefsRec ts

extractWhere :: QueryExpr -> [AExpr String]
extractWhere query =
    let scalarExprs = extractWhereExpr query in
    map extractScalarExpr scalarExprs

extractScalarExpr :: ScalarExpr -> AExpr String
extractScalarExpr expr =
    case expr of
        Identifier _ (Name _ nmcs) -> AVar $ intercalate "." (map (\(Nmc x) -> x) nmcs)
        NumberLit _ s -> AConst (read s)
        StringLit _ s -> AText s
        BinaryOp _ (Name _ [Nmc "<="]) x1 x2 -> ABinary ALT (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc "<"]) x1 x2 -> ABinary ALT (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc "="]) x1 x2 -> ABinary AEQ (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc "<>"]) x1 x2 -> AUnary ANot $ ABinary AEQ (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc "!="]) x1 x2 -> AUnary ANot $ ABinary AEQ (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc ">"]) x1 x2 -> ABinary AGT (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc ">="]) x1 x2 -> ABinary AGT (extractScalarExpr x1) (extractScalarExpr x2)

        BinaryOp _ (Name _ [Nmc "like"]) x1 x2 -> ABinary ALike (extractScalarExpr x1) (extractScalarExpr x2)

        BinaryOp _ (Name _ [Nmc "and"]) x1 x2 -> ABinary AAnd (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc "or"]) x1 x2  -> ABinary AOr (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc "xor"]) x1 x2 -> ABinary AXor (extractScalarExpr x1) (extractScalarExpr x2)

        BinaryOp _ (Name _ [Nmc "*"]) x1 x2 -> ABinary AMult (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc "/"]) x1 x2 -> ABinary ADiv (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc "+"]) x1 x2 -> ABinary AAdd (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc "-"]) x1 x2 -> ABinary ASub (extractScalarExpr x1) (extractScalarExpr x2)

        BinaryOp _ (Name _ [Nmc "^"]) x1 x2 ->
            let z2 = extractScalarExpr x2 in
                case z2 of
                    AConst c -> AUnary (APower c) (extractScalarExpr x1)
                    _        -> error $ error_queryExpr expr
        PrefixOp _ (Name _ [Nmc "not"]) x -> AUnary ANot (extractScalarExpr x)
        PrefixOp _ (Name _ [Nmc "-"])   x -> AUnary ANeg (extractScalarExpr x)

        App _ (Name _ [Nmc "abs"]) [x] -> AAbs (extractScalarExpr x)
        App _ (Name _ [Nmc "log"]) [x] -> AUnary ALn (extractScalarExpr x)
        App _ (Name _ [Nmc "exp"]) [x] -> AUnary (AExp 1.0) (extractScalarExpr x)
        App _ (Name _ [Nmc "least"])    xs -> AMins (map extractScalarExpr xs)
        App _ (Name _ [Nmc "greatest"]) xs -> AMaxs (map extractScalarExpr xs)

        Star _ -> AConst 0.0
        Parens _ x -> extractScalarExpr x

        SpecialOp _ (Name _ [Nmc "between"]) [x,x1,x2] -> ABinary AAnd (ABinary AGT (extractScalarExpr x) (extractScalarExpr x1)) (ABinary AGT (extractScalarExpr x2) (extractScalarExpr x))
        InPredicate _ x True (InList _ xs) -> foldr (\ae aes -> ABinary AOr (ABinary AEQ b ae) aes) (ABinary AEQ b a) as
                                              where (a:as) = map extractScalarExpr xs
                                                    b      = extractScalarExpr x

        _        -> error $ error_queryExpr expr


extractWhereExpr :: QueryExpr -> [ScalarExpr]
extractWhereExpr query =
  maybeToList (selWhere query) ++
  [e | JoinTref a _ _ _ _ _ (Just (JoinOn _ e)) <- universeBi query]

extractJoinTables :: QueryExpr -> [TableRef]
extractJoinTables = concatMap go . selTref
  where
    go (JoinTref _ l _ _ _ r _) = go l ++ go r
    go t = [t]

typeCheckSelectQuery :: Dialect -> Bool -> Bool -> FilePath -> Catalog -> QueryExpr -> IO QueryExpr
typeCheckSelectQuery dialect local checkUnsupporteds fp catalog query = do
  query <- return $ typeCheckQueryExpr typeCheckFlags catalog query
  queryErrs <- checkAndReportErrors query
  when queryErrs exitFailure -- dont bail?
  -- Because type checker may rewrite queries to a different form
  -- we perform feature check late.
  bailRef <- newIORef False
  when checkUnsupporteds $ do
    forM_ (unsupportedClauses local query) $ \str -> do
      bailRef `writeIORef` True
      err $ str ++ " clause is not supported"
    forM_ (unsupportedFrom local query) $ \ (loc, str) -> do
      bailRef `writeIORef` True
      err $ prettyLoc (printf "%s not supported in FROM clause." str) loc
    forM_ (unsupportedWhere local query) $ \loc -> do
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
