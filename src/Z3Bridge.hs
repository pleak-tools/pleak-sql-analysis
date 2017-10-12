{-# LANGUAGE LambdaCase #-}

module Z3Bridge (
  dbFromCatalogUpdates,
  dbUniqueInfoFromStatements,
  generateZ3,
  findPrimaryKeys,
  performAnalysis,
  printAnalysisResults,
  printCombinedAnalysisResults,
  analysisResultsToInts,
  combineAnalysisResults,
  alternativeAnalysisResults,
  extractTableNames)
  where

import Control.Arrow
import Control.Concurrent
import Control.Concurrent.Async
import Control.Monad
import Data.Char
import Data.Data
import Data.List
import Data.Map (Map)
import Data.Maybe
import Data.Text (unpack, pack)
import Database.HsSqlPpp.Annotation
import Database.HsSqlPpp.Catalog
import Database.HsSqlPpp.Syntax
import Database.HsSqlPpp.Types
import Text.Printf
import System.IO
import System.Process

import qualified Data.Map as Map
import qualified Data.Set as Set

import Logging
import ProgramOptions
import Schema
import SelectQuery

--------------------------------------
-- Some generic Z3 code gen helpers --
--------------------------------------

-- function concat (or something)
fcat :: [a -> a] -> a -> a
fcat = foldr (.) id

showP :: ShowS -> ShowS
showP s = showChar '(' . s . showChar ')'

space :: ShowS
space = showChar ' '

spaced :: ShowS -> ShowS -> ShowS
spaced x y = x . space . y

sepBySpace :: [ShowS] -> ShowS
sepBySpace = fcat . intersperse space

sepByHyphen :: [ShowS] -> ShowS
sepByHyphen = fcat . intersperse (showChar '-')

nl :: ShowS
nl = showChar '\n'

z3Push :: ShowS
z3Push = showString "(push)\n"

z3Pop :: ShowS
z3Pop = showString "(pop)\n"

z3CheckSat :: ShowS
z3CheckSat = showString "(check-sat)\n"

z3Assert :: ShowS -> ShowS
z3Assert s = showP (showString "assert" `spaced` s) . nl

z3Eq :: [ShowS] -> ShowS
z3Eq as = showP $ sepBySpace $ showString "=" : as

z3Distinct :: [ShowS] -> ShowS
z3Distinct as = showP $ sepBySpace $ showString "distinct" : as

z3Or :: [ShowS] -> ShowS
z3Or es = showP (showString "or" `spaced` sepBySpace es)

z3And :: [ShowS] -> ShowS
z3And es = showP (showString "and" `spaced` sepBySpace es)

z3Impl :: ShowS -> ShowS -> ShowS
z3Impl e1 e2 = showP $ showString "=>" `spaced` e1 `spaced` e2

z3DeclareConst :: ShowS -> ShowS -> ShowS
z3DeclareConst var ty = showP (showString "declare-const" `spaced` var `spaced` ty) . nl

z3DeclareFun :: ShowS -> [ShowS] -> ShowS -> ShowS
z3DeclareFun name args ret =
  showP (showString "declare-fun" `spaced`
         name `spaced`
         showP (sepBySpace args) `spaced`
         ret) . nl

------------------------------------
-- Information about the database --
------------------------------------

-- TODO: move to Schema.hs
-- clean up in general

type TableInfo = [(CatName, CatName)]
type DbSchema = Map CatName TableInfo
type UniqueInfo = [(Name, [[NameComponent]])]

dbFromCatalogUpdates :: [CatalogUpdate] -> DbSchema
dbFromCatalogUpdates us = Map.fromList [(n, map (second catName) cols) | CatCreateTable (_, n) cols <- us]

dbUniqueInfoFromStatements :: [Statement] -> UniqueInfo
dbUniqueInfoFromStatements = map go
  where
    go stmt = (extractName stmt, extractUniques stmt)

---------------------------
-- Generate Z3 statement --
---------------------------

exprFromSelectItem :: SelectItem -> ScalarExpr
exprFromSelectItem (SelExp _ e) = e
exprFromSelectItem (SelectItem _ e _) = e

getScalarTypeFromAnn :: Data a => a -> Maybe CatName
getScalarTypeFromAnn x = (getScalarType . teType) <$> anType (getAnnotation x)
  where
    getScalarType = \case
      ScalarType t -> t
      _ -> ice "Invalid type."

getSelects :: QueryExpr -> [(CatName, ScalarExpr)]
getSelects query = do
  let SelectList _ ss = selSelectList query
  e <- exprFromSelectItem <$> ss
  t <- case getScalarTypeFromAnn e of
    Nothing -> ice "Expecting type annotation here."
    Just t -> return t
  return (t, e)

performAnalysis :: ProgramOptions -> UniqueInfo -> DbSchema -> QueryExpr -> IO (Either ([CatName], [SatResult]) ([CatName], [Int]))
performAnalysis opts us s q = do
  when (debugPrintZ3 opts) $
    hPutStrLn stderr z3Input
  if sensitivity opts == -1
    then do
      results <- forM tables (analyzeOneTable (z3Path opts) us'' s'' q'')
      return $ Right (tables',results)
    else do
      result <- sendToZ3 (z3Path opts) tables z3Input
      results <- case result of
        Nothing -> fatal "Z3 timed out."
        Just rs -> return rs
      return $ Left (tables', results)
  where
    q' = if null (selGroupBy q) then q else transformGroupBy q
    (us'',s'',q'',aliasToOrigTableMap) = transformTableAliases us s q'
    (tables, doc) = second fcat $ unzip $ generateZ3 us'' s'' q'' (sensitivity opts)
    tables' = map (aliasToOrigTableMap Map.!) tables
    z3Input = doc ""

analyzeOneTable :: Maybe FilePath -> UniqueInfo -> DbSchema -> QueryExpr -> CatName -> IO Int
analyzeOneTable fp us s q t = do
  let genZ3 n = generateZ3Go us s q n t Nothing
  let invokeZ3 n = sendToZ3 fp [t] (genZ3 n "")
  let
    try n = if n > 10 then return (-1) else do
      res <- invokeZ3 n
      case res of
        Nothing        -> return (-1)
        Just [Unknown] -> do printf "sensitivity not known on %s (Z3 yielded unknown)\n" (unpack t)
                             return (-1)
        Just [Unsat]   -> do printf "<= %d sensitive on %s\n" n (unpack t)
                             return n
        Just [Sat]     -> do printf "> %d sensitive on %s\n" n (unpack t)
                             try (n+1)
  try 1

-- replace a GROUP BY query by a non-GROUP BY query with the same sensitivity bound
transformGroupBy :: QueryExpr -> QueryExpr
transformGroupBy q = q {selSelectList = SelectList err newSelectList, selGroupBy = [], selDistinct = Distinct}
  where
    err = error "transformGroupBy"
    newSelectList = map (\ x -> SelectItem err x (Nmc err)) (selGroupBy q)

transformTableAliases :: UniqueInfo -> DbSchema -> QueryExpr -> (UniqueInfo, DbSchema, QueryExpr, Map CatName CatName)
transformTableAliases us s q = (us', s', q {selTref = st'}, aliasToOrigTableMap)
  where
    err = error "transformTableAliases"
    (st', tableAliases, tableOrigs) = unzip3 $ map (
      \case
        TableAlias _ ta (Tref _ (Name _ [t0])) -> (Tref err (Name err [ta]), ta, t0)
        tr@(Tref _ (Name _ [t])) -> (tr, t, t)
      ) (selTref q)
    nameAliases (Name _ [t]) = map (Name err . (:[])) $ Map.findWithDefault [] t (Map.fromList (listGroups (zip tableOrigs tableAliases)))
    us' = [(tbl',colss) | (tbl,colss) <- us, tbl' <- nameAliases tbl]
    tas = map nameComponentToCatName tableAliases
    t0s = map nameComponentToCatName tableOrigs
    s' = Map.fromList $ map (second fromJust) $ filter (isJust . snd) $ zipWith (\ ta t0 -> (ta, Map.lookup t0 s)) tas t0s
    aliasToOrigTableMap = Map.fromList $ zip tas t0s

findPrimaryKeys :: ProgramOptions -> UniqueInfo -> DbSchema -> QueryExpr -> IO [Bool]
findPrimaryKeys opts us s q = do
  when (debugPrintZ3 opts) $ do
    hPutStrLn stderr "---"
    hPutStrLn stderr z3Input
    hPutStrLn stderr "---"
  result <- sendToZ3 (z3Path opts) (map (const (pack "")) selects) z3Input
  results <- case result of
    Nothing -> fatal "Z3 timed out."
    Just rs -> return rs
  return (map (== Unsat) results)
  where
    selects = getSelects q
    z3Input = generatePrimaryKeyZ3 us s q ""

printAnalysisResults :: ProgramOptions -> ([CatName], [SatResult]) -> IO ()
printAnalysisResults opts (tables, results) =
  forM_ (zip tables results) $ \(t, r) ->
    putStrLn $ case r of
      Sat -> printf "> %d sensitive on %s" (sensitivity opts) (unpack t)
      Unsat -> printf "<= %d sensitive on %s" (sensitivity opts) (unpack t)
      Unknown -> yellow $ printf "sensitivity not known on %s (Z3 yielded unknown)" (unpack t)
      Bad str -> red $ printf "on table %s Z3 failed on with: %s" (unpack t) str

printCombinedAnalysisResults :: [(CatName, Int)] -> IO ()
printCombinedAnalysisResults res =
  forM_ res $ \ (t, r) -> printf "upper bound of sensitivity on table %s: %d\n" t r

sumGroupsWith :: (Ord a, Ord b) => ([b] -> b) -> [(a,b)] -> [(a,b)]
sumGroupsWith sumf = map (\ g -> (fst (head g), sumf (map snd g))) . groupBy (\ x y -> fst x == fst y) . sort

listGroups :: (Ord a, Ord b) => [(a,b)] -> [(a,[b])]
listGroups = sumGroupsWith concat . map (second (:[]))

combineAnalysisResults :: [([CatName], [Int])] -> [(CatName, Int)]
combineAnalysisResults ress = sumGroupsWith sumWithInfinity (zip cns is)
  where
    (cnss, srss) = unzip ress
    cns = concat cnss
    is = concat srss

    sumWithInfinity [] = 0
    sumWithInfinity (x : xs) | x < 0 || y < 0 = min x y
                             | otherwise      = x + y
                           where
                             y = sumWithInfinity xs

analysisResultsToInts :: ProgramOptions -> ([CatName], [SatResult]) -> ([CatName], [Int])
analysisResultsToInts opts res = second (map resultToInt) res
  where
    resultToInt :: SatResult -> Int
    resultToInt Sat = -1
    resultToInt Unsat = sensitivity opts
    resultToInt _ = -1


--analysisResultsToInts :: ProgramOptions -> [([CatName], [SatResult])] -> [(CatName, Int)]
--analysisResultsToInts opts ress = sumGroupsWith sumWithInfinity (zip cns is)
--  where
--    (cnss, srss) = unzip ress
--    cns = concat cnss
--    srs = concat srss
--    is = map resultToInt srs
--
--    sumWithInfinity [] = 0
--    sumWithInfinity (x : xs) | x < 0 || y < 0 = min x y
--                             | otherwise      = x + y
--                           where
--                             y = sumWithInfinity xs
--
--    resultToInt :: SatResult -> Int
--    resultToInt Sat = -1
--    resultToInt Unsat = sensitivity opts
--    resultToInt _ = -1


alternativeAnalysisResults :: [[CatName]] -> [(CatName, Int)] -> [Int]
alternativeAnalysisResults tableNamess results =
  map (combineResInts . map (flip (Map.findWithDefault 0) (Map.fromList results))) tableNamess
  where
    combineResInts [] = 0
    combineResInts (x : xs) | x < 0 || y < 0 = min x y
                            | otherwise      = max x y
                          where
                            y = combineResInts xs

extractTableNames :: [Statement] -> [CatName]
extractTableNames = concatMap extractTableName
  where
    extractTableName (CreateTable _ n _ _ _ _ _) = [nameToCatName n]
    extractTableName _ = []

-- TODO: partial
-- ^ Generate Z3 code to verify if query is <= 1 sensitive
generateZ3 :: UniqueInfo         -- ^ uniques
           -> DbSchema           -- ^ information about the database
           -> QueryExpr          -- ^ query
           -> Int                -- ^ sensitivity
           -> [(CatName, ShowS)]
generateZ3 us s query n = map (\t -> (t, generateZ3Go us s query n t Nothing)) uniqueJoinTables
  where
    joinTables = map (nameToCatName.getName) $ extractJoinTables query
    uniqueJoinTables = nub joinTables
    getName (Tref _ n) = n -- TODO: obviously...

generateZ3Go :: UniqueInfo         -- ^ uniques
             -> DbSchema           -- ^ information about the database
             -> QueryExpr          -- ^ query
             -> Int                -- ^ sensitivity
             -> CatName
             -> Maybe ScalarExpr
             -> ShowS
generateZ3Go us s query n = go
  where
    joinTables = map (nameToCatName.getName) $ extractJoinTables query
    selects = getSelects query

    uniqueJoinTables = nub joinTables

    -- XXX: does not consider nested queries!
    schema = Map.filterWithKey (\k v -> k `elem` uniqueJoinTables) s

    uniqueAsserts fixedTable = fcat [genUnique schema fixedTable tbl cols n | (tbl, colss) <- us, cols <- colss]
    whereAsserts fixedTable = fcat $ map (genWhere schema fixedTable n) $ extractWhereExpr query
    mkTuple = showString "mk-tuple"
    funDecl = z3DeclareFun mkTuple (map (genType.fst) selects) (showString "Int")

    colEqAsserts fixedTable e = z3Assert $ z3Eq $ take 2 $ genScalarExpr' fixedTable e

    distinctAsserts fixedTable = let
        ess = transpose [take (n + 1) $ genScalarExpr' fixedTable e | (_, e) <- selects]
      in z3Assert $ z3Distinct $ map (\es -> showP $ mkTuple `spaced` sepBySpace es) ess

    getName (Tref _ n) = n -- TODO: obviously...

    go fixedTable se = id
      . z3Push
      . genDecls schema fixedTable n
      . uniqueAsserts fixedTable
      . whereAsserts fixedTable
      . funDecl
      . (case se of Just e -> colEqAsserts fixedTable e; Nothing -> id)
      . distinctAsserts fixedTable
      . z3CheckSat
      . z3Pop

generatePrimaryKeyZ3 :: UniqueInfo         -- ^ uniques
                     -> DbSchema           -- ^ information about the database
                     -> QueryExpr          -- ^ query
                     -> ShowS
generatePrimaryKeyZ3 us s query = fcat $ map (generateZ3Go us s query 1 (pack "") . Just) (map snd $ getSelects query)


nameComponentToCatName :: NameComponent -> CatName
nameComponentToCatName n = pack $ genNameComponent n ""

nameToCatName :: Name -> CatName
nameToCatName n = pack $ genName n ""

genName :: Name -> ShowS
genName (AntiName n) = showString n
genName (Name _ ns) = fcat $ intersperse (showString "-") $ map genNameComponent ns

-- TODO: "IS" and "IS NOT" dont work the same way as "=" and "!="
--       unless we assume that everything is NOT NULL (which we do)
genOp :: Name -> ShowS
genOp n = maybe (ice errMsg) id $ lookup n' ops
  where
    n' = map toLower (genName n "")
    errMsg  = printf "Undefined operator \"%s\"" n'
    ops = map (second showString) [
        ("not", "not"),
        ("or", "or"),
        ("and", "and"),
        ("<>", "distinct"), ("!=", "distinct"), ("is not", "distinct"),
        ("*", "*"), ("+", "+"), ("-", "-"), ("/", "/"), ("%", "%"),
        ("=", "="), ("<", "<"), ("<=", "<="), (">", ">"), (">=", ">=")
      ]

-- TODO: variables of those types have extra constraints!
genType :: CatName -> ShowS
genType n = showString $ case unpack n of
  "int2"    -> "Int"
  "int4"    -> "Int"
  "int8"    -> "Int"
  "integer" -> "Int"
  "int"     -> "Int"
  "date"    -> "Int"
  "bool"    -> "Bool"
--  "text"    -> "String"
  "text"    -> "(Seq (_ BitVec 8))"
  "double precision" -> "Real"
  n'        -> ice $ printf "Invalid type \"%s\"." n'

genNameComponent :: NameComponent -> ShowS
genNameComponent = showString . ncStr
--genNameComponent (Nmc s) = showString s
--genNameComponent (QNmc s) = showString s
--genNameComponent (AntiNameComponent s) = showString s

genCatName :: CatName -> ShowS
genCatName = showString . unpack

genColNamePrefix :: CatName -> CatName -> ShowS
genColNamePrefix tbl row = genCatName tbl . showChar '-' . genCatName row

genColName :: CatName -> CatName -> ShowS -> ShowS
genColName tbl row suffix = genColNamePrefix tbl row . suffix

-- TODO: get rid of duplicates
genWhere :: DbSchema -> CatName -> Int -> ScalarExpr -> ShowS
genWhere schema fixed n e = fcat (map z3Assert es)
  where es = take (n + 1) $ genScalarExpr' fixed e

genDecls :: DbSchema -> CatName -> Int -> ShowS
genDecls schema fixed n = fcat $ concatMap go $ Map.toList schema
  where
    go (tbl, cols)
      | tbl == fixed = map (goFixed tbl) cols
      | otherwise = map (goVariable tbl) cols

    goFixed tbl col = let
        name = genColNamePrefix tbl (fst col)
      in z3DeclareConst name (genType (snd col))

    goVariable tbl col = let
        ty = genType (snd col)
        name i = genColName tbl (fst col) (showString "-" . shows i)
        decl i = z3DeclareConst (name i) ty
      in fcat [decl i | i <- [1 .. n + 1]]

---- ^ Assumes that "tbl" is not the one that is fixed!
--genUnique :: DbSchema -> CatName -> Name -> [NameComponent] -> Int -> ShowS
--genUnique schema fixedTable tbl us n
--  | tblName == fixedTable = id
--  | null otherColNames = id
--  | otherwise = z3Assert (precond `z3Impl` postcond)
--  where
--    tblName = nameToCatName tbl
--    usNames = map nameComponentToCatName us
--    uniqueColNames = map (genColNamePrefix tblName) usNames
--    mk i x = x . showString "-" . shows i
--
--    precond = z3And $ do
--      name <- uniqueColNames
--      i <- [1 .. n + 1]
--      j <- [i + 1 .. n + 1]
--      return $ z3Eq [mk i name, mk j name]
--
--    mkEq name = z3Eq [mk i name | i <- [1 .. n + 1]]
--    postcond = z3And $ map mkEq otherColNames
--
--    -- TODO: only own table?
--    otherColNames = do
--      (tbl', cols) <- Map.toList schema
--      guard $ fixedTable /= tbl'
--      -- only own table
--      guard $ tbl' == tblName
--      (col, _) <- cols
--      return $ genColNamePrefix tbl' col

-- ^ Assumes that "tbl" is not the one that is fixed!
genUnique :: DbSchema -> CatName -> Name -> [NameComponent] -> Int -> ShowS
genUnique schema fixedTable tbl us n
  | tblName == fixedTable = id
  | null otherColNames = id
  | otherwise = genUnique1
  where
    mk i x = x . showString "-" . shows i
    -- genUnique1 and genUnique2 describe the same model but the former with O(n) input and the latter with O(n^2) input size to Z3.
    genUnique1 = fcat $
      zipWith (\ ocn oct ->
          let
            funName = sepByHyphen uniqueColNames . showString "-to-" . ocn
          in
            z3DeclareFun funName (ucTypes) oct .
            fcat (do
              i <- [1 .. n + 1]
              return $ z3Assert $ z3Eq [mk i ocn, showP (funName `spaced` sepBySpace (map (mk i) uniqueColNames))]))
        otherColNames ocTypes
    genUnique2 = fcat $ do
      i <- [1 .. n + 1]
      j <- [i + 1 .. n + 1]
      return $ genUnique' schema fixedTable tblName uniqueColNames otherColNames i j
    usNames = map nameComponentToCatName us
    --uniqueColNames = map (genColNamePrefix tblName) usNames
    usNamesSet = Set.fromList usNames
    tblName = nameToCatName tbl
    -- TODO: only own table?
    (otherColNames, ocTypes) = unzip $ do
      (tbl', cols) <- Map.toList schema
      guard $ fixedTable /= tbl'
      -- only own table
      guard $ tbl' == tblName
      (col, colt) <- cols
      guard $ Set.notMember col usNamesSet
      return (genColNamePrefix tbl' col, genType colt)
    (uniqueColNames, ucTypes) = unzip $ do
      (tbl', cols) <- Map.toList schema
      guard $ fixedTable /= tbl'
      guard $ tbl' == tblName
      (col, colt) <- cols
      guard $ Set.member col usNamesSet
      return (genColNamePrefix tbl' col, genType colt)

genUnique' :: DbSchema -> CatName -> CatName -> [ShowS] -> [ShowS] -> Int -> Int -> ShowS
genUnique' schema fixedTable tblName uniqueColNames otherColNames u v = z3Assert (precond `z3Impl` postcond)
  where
    mk i x = x . showString "-" . shows i

    precond = z3And $ do
      name <- uniqueColNames
      return $ z3Eq [mk u name, mk v name]

    mkEq name = z3Eq [mk i name | i <- [u,v]]
    postcond = z3And $ map mkEq otherColNames

-- TODO: quite inefficient
genScalarExpr' :: CatName -> ScalarExpr -> [ShowS]
genScalarExpr' fixed e = [genScalarExpr (showIdent i) e | i <- [1 ..]]
  where
    showIdent i (Name _ [q, n])
      | q' == fixed = genColName q' n' id
      | otherwise = genColName q' n' (showChar '-' . shows i)
      where
        q' = nameComponentToCatName q
        n' = nameComponentToCatName n

-- TODO: function calls
genScalarExpr :: (Name -> ShowS) -> ScalarExpr -> ShowS
genScalarExpr showIdent = go
  where
    go = \case
      Identifier _ n -> showIdent n
      NumberLit _ s -> showString s
      BooleanLit _ b -> shows b
      StringLit _ s -> shows s -- TODO: relying on how haskell shows strings
      Parens _ e -> go e
      PrefixOp _ op e -> showP $ genOp op `spaced` go e
      BinaryOp _ op e1 e2 -> showP $ genOp op `spaced` go e1 `spaced` go e2
      SpecialOp _ op [e1,e2,e3] | map toLower (genName op "") == "between" ->
        let
          goe1 = go e1
        in
          showP (showString "and" `spaced` (showP (showString ">=" `spaced` goe1 `spaced` go e2))
                                  `spaced` (showP (showString "<=" `spaced` goe1 `spaced` go e3)))
      App _ op [_] | isSupportedAggregOp op ->
        showString "0"
      _ -> ice "Invalid scalar expression." -- TODO: location

-------------------------
-- Interaction with Z3 --
-------------------------

data SatResult
  = Unsat
  | Sat
  | Unknown
  | Bad String
  deriving Eq

readSatResultZ3 :: String -> SatResult
readSatResultZ3 = \case
  "unsat"   -> Unsat
  "sat"     -> Sat
  "unknown" -> Unknown
  str       -> Bad str

withTimeout :: Int -> IO a -> IO (Maybe a)
withTimeout timeout act  = either Just (const Nothing) <$> race act (threadDelay timeout)

sendToZ3 :: Maybe FilePath -> [CatName] -> String -> IO (Maybe [SatResult])
sendToZ3 z3Path tbls msg = do
  let z3Command = fromMaybe "z3" z3Path
  --let cmdArgs = ["-smt2", "-in", "-T:310", "-t:300000"]
  let cmdArgs = ["-smt2", "-in", "-T:15", "-t:5000"]
  (Just hin, Just hout, _, procHandle) <- createProcess (proc z3Command cmdArgs) {
    std_in  = CreatePipe,
    std_out = CreatePipe
  }

  hPutStrLn hin msg
  hFlush hin

  --result <- withTimeout 310000000 $ do
  result <- withTimeout 15000000 $ do
    rs <- forM tbls $ \_ ->
      readSatResultZ3 <$> hGetLine hout
    hClose hin
    hClose hout
    return rs

  exitCode <- getProcessExitCode procHandle
  case exitCode of
    Nothing -> terminateProcess procHandle
    Just _ -> return ()

  return result
