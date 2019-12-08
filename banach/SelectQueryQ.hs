{-# LANGUAGE LambdaCase #-}

module SelectQueryQ (
  parseQuery,
  parseQueryMap,
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

import Debug.Trace

import qualified Data.Map as M
import qualified Data.Text.Lazy as T

import SchemaQ -- TODO: workaround
import LoggingQ

import ExprQ
import AexprQ
import QueryQ
import ErrorMsg

data Query
  = P [String] [Function] (M.Map TableAlias TableName) [AExpr VarName]
  deriving (Show)

parseQueryMap :: String -> String -> IO (TableName, M.Map TableName QueryQ.Query)
parseQueryMap defaultOutputName s = do
    queries <- parseNamedQuery defaultOutputName s
    let outputTableName = fst $ last queries
    let subQueryMaps = map (\(name,query) -> constructSubQueries name query) queries
    let queryMap = foldr M.union M.empty subQueryMaps
    return (outputTableName, queryMap)

constructSubQueries :: TableName -> QueryExpr -> (M.Map TableName QueryQ.Query)
constructSubQueries tableName queryExpr =
    let (tableAliasMap, subQueries) = extractTrefs queryExpr in
    let funs = extractSelect tableName queryExpr in
    let filters = extractWhere queryExpr in
    let groups = extractGroups queryExpr in
    let subQuery = QueryQ.P groups funs tableAliasMap filters in
    M.insert tableName subQuery subQueries

parseNamedQuery :: String -> String -> IO [(String, QueryExpr)]
parseNamedQuery defaultOutputName s = do
    xs <- parseSchemas s
    return $ map (extractNameAndQuery defaultOutputName) xs

extractNameAndQuery :: String -> Statement -> (String, QueryExpr)
extractNameAndQuery _ (Insert _ (Name _ [Nmc name]) _ query _) = (name, query)
extractNameAndQuery defaultOutputName (QueryStatement _ query) = (defaultOutputName, query)

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
  App _ n _        -> nameToStr n `elem` apps
  InPredicate _ _ True (InList _ _) -> True
  _                -> False
  where
    ops = ["=", "<", ">", "<=", ">=", "<>", "<@>", "and", "or", "xor", "+", "-", "*", "/", "%", "^", "not"]
    apps = ["log", "exp", "abs", "least", "greatest","point"]

isSupportedAggregOp :: Name -> Bool
isSupportedAggregOp op = nameToStr op `elem` ["count", "sum", "avg", "min", "max"]

nameToStr :: Name -> String
nameToStr (Name _ ns) = intercalate "." (map ncStr ns)
nameToStr AntiName{} = ice "Unexpected AntiName."

extractSelect :: String -> QueryExpr -> [Function]
extractSelect tableName query =
    let y = tableName in
    let (SelectList _ xs) = selSelectList query in
    zipWith (extractTableExpr tableName) xs [0..length xs - 1]

extractTableExpr :: String -> SelectItem -> Int -> Function
extractTableExpr _ (SelExp _ (App _ (Name _ [Nmc aggrOp]) [expr])) i =
    let y = "y" ++ (show i) in
    let arg = extractScalarExpr expr in
    let aggrOp2 = map toLower aggrOp in
    case aggrOp2 of
        "count" -> F arg (SelectCount y)
        "sum"   -> F arg (SelectSum y)
        "avg"   -> F arg (SelectAvg y)
        "min"   -> F arg (SelectMin y)
        "max"   -> F arg (SelectMax y)
        _       -> error $ error_queryExpr_aggrFinal aggrOp

extractTableExpr _ (SelectItem _ (App _ (Name _ [Nmc aggrOp]) [expr]) (Nmc colName)) _ =
    let y = colName in
    let arg = extractScalarExpr expr in
    let aggrOp2 = map toLower aggrOp in
    case aggrOp2 of
        "count" -> F arg (SelectCount y)
        "sum"   -> F arg (SelectSum y)
        "avg"   -> F arg (SelectAvg y)
        "min"   -> F arg (SelectMin y)
        "max"   -> F arg (SelectMax y)
        _       -> error $ error_queryExpr_aggrFinal aggrOp

-- TODO prefix would be needed if we treat all subqueries as subtables
-- currently, we treat plain select statements in a different way
extractTableExpr _ (SelectItem _ expr (Nmc colName)) _ =
    let arg = extractScalarExpr expr in
    F arg (SelectPlain colName)

extractTableExpr _ (SelExp _ (Identifier _ (Name _ [Nmc tableName, Nmc colName]))) _ = 
    let varName = tableName ++ "." ++ colName in
    F (AVar varName) (SelectPlain varName)

extractTableExpr _ (SelExp _ (Identifier _ (Name _ [Nmc colName]))) _ = error $ error_queryExpr_unnamed colName

extractTableExpr _ q _ = error $ error_queryExpr q

extractTrefs :: QueryExpr -> (M.Map TableName TableAlias, M.Map TableName QueryQ.Query)
extractTrefs query = extractTrefsRec (selTref query) M.empty M.empty

extractTrefsRec :: [TableRef] -> M.Map TableName TableAlias -> M.Map TableName QueryQ.Query -> (M.Map TableName TableAlias, M.Map TableName QueryQ.Query)
extractTrefsRec [] ts qs = (ts, qs)
extractTrefsRec (TableAlias _ (Nmc tableAlias) (Tref _ (Name _ [Nmc tableName])):xs) ts qs  =
    let (ts', qs') = extractTrefsRec xs ts qs in
    (M.insert tableAlias tableName ts', qs')

extractTrefsRec (Tref _ (Name _ [Nmc tableName]):xs) ts qs  =
    let (ts', qs') = extractTrefsRec xs ts qs in
    (M.insert tableName tableName ts', qs')

extractTrefsRec (TableAlias _ (Nmc tableName) (SubTref _ queryExpr):xs) ts qs  =
    let (ts', qs1) = extractTrefsRec xs ts qs in
    let qs2 = constructSubQueries tableName queryExpr in
    (M.insert tableName tableName ts', M.union qs1 qs2)

extractTrefsRec (JoinTref _ x1 _ _ _ x2 _:xs) ts qs =
    extractTrefsRec (x1:x2:xs) ts qs

--extractTrefsRec t _ _ = error $ error_queryExpr t

extractWhere :: QueryExpr -> [AExpr String]
extractWhere query =
    let scalarExprs = extractWhereExpr query in
    let aexprs = map extractScalarExpr scalarExprs in
    concat $ map applyAexprNormalize aexprs

extractGroups :: QueryExpr -> [String]
extractGroups query =
    let scalarExprList = selGroupBy query in
    map (\ (Identifier _ (Name _ nmcs)) ->  intercalate "." (map (\(Nmc x) -> x) nmcs)) scalarExprList

applyAexprNormalize :: AExpr String -> [AExpr String]
applyAexprNormalize bexpr =
    let aexpr = aexprNormalize bexpr in
    -- how many filters we actually have if we split them by "and"?
    let xs = case aexpr of
            AAnds ys -> ys
            _        -> []
    in if length xs == 0 then [aexpr] else xs

extractScalarExpr :: ScalarExpr -> AExpr String
extractScalarExpr expr =
    --trace (show expr) $
    case expr of
        Identifier _ (Name _ nmcs) -> AVar $ intercalate "." (map (\(Nmc x) -> x) nmcs)
        NumberLit _ s -> AConst (read s)
        StringLit _ s -> AText ("\'" ++ s ++ "\'")
        BinaryOp _ (Name _ [Nmc "<>"]) x1 x2 -> AUnary ANot $ ABinary AEQ (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc "<@>"]) x1 x2 -> ABinary ADistance (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc "<="]) x1 x2 -> ABinary ALE (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc "<"]) x1 x2 -> ABinary ALT (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc "="]) x1 x2 -> ABinary AEQ (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc "!="]) x1 x2 -> AUnary ANot $ ABinary AEQ (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc ">="]) x1 x2 -> ABinary AGE (extractScalarExpr x1) (extractScalarExpr x2)
        BinaryOp _ (Name _ [Nmc ">"]) x1 x2 -> ABinary AGT (extractScalarExpr x1) (extractScalarExpr x2)

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
        App _ (Name _ [Nmc "floor"]) [x] -> AUnary AFloor (extractScalarExpr x)
        App _ (Name _ [Nmc "exp"]) [x] -> AUnary (AExp 1.0) (extractScalarExpr x)
        App _ (Name _ [Nmc "least"])    xs -> AMins (map extractScalarExpr xs)
        App _ (Name _ [Nmc "greatest"]) xs -> AMaxs (map extractScalarExpr xs)
        App _ (Name _ [Nmc "point"]) xs -> AVector (map extractScalarExpr xs)

        Star _ -> AConst 0.0
        Parens _ x -> extractScalarExpr x

        SpecialOp _ (Name _ [Nmc "between"]) [x,x1,x2] -> ABinary AAnd (ABinary AGE (extractScalarExpr x) (extractScalarExpr x1)) (ABinary AGE (extractScalarExpr x2) (extractScalarExpr x))
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
