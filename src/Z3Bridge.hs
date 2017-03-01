{-# LANGUAGE LambdaCase #-}

module Z3Bridge (
  dbFromCatalogUpdates,
  dbUniqueInfoFromStatements,
  generateZ3)
  where

import Control.Arrow
import Data.Char
import Data.Data
import Data.List
import Data.Map (Map)
import Data.Text (unpack, pack)
import Database.HsSqlPpp.Annotation
import Database.HsSqlPpp.Catalog
import Database.HsSqlPpp.Syntax
import Database.HsSqlPpp.Types
import Text.Printf

import qualified Data.Map as Map

import Logging
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

nl :: ShowS
nl = showChar '\n'

z3Push :: ShowS
z3Push = showString "(push)\n"

z3Pop :: ShowS
z3Pop = showString "(pop)\n"

z3CheckSat :: ShowS
z3CheckSat = showString "(check-sat)\n"

z3Isolate :: ShowS -> ShowS
z3Isolate s = z3Push . s . z3Pop

z3Assert :: ShowS -> ShowS
z3Assert s = showP (showString "assert" `spaced` s) . nl

z3Eq :: ShowS -> ShowS -> ShowS
z3Eq e1 e2 = showP $ showChar '=' `spaced` e1 `spaced` e2

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

z3Distinct :: [ShowS] -> ShowS
z3Distinct as = showP (sepBySpace (showString "distinct" : as))

------------------------------------
-- Information about the database --
------------------------------------

-- TODO: move to Schema.hs
-- clean up in general

type TableInfo = [(CatName, CatName)]
type DbSchema = Map CatName TableInfo
type UniqueInfo = [(Name, [[NameComponent]])]

dbTables :: DbSchema -> [CatName]
dbTables = map fst . Map.toList

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

-- TODO: partial
-- ^ Generate Z3 code to verify if query is <= 1 sensitive
generateZ3 :: UniqueInfo         -- ^ uniques
           -> DbSchema           -- ^ information about the database
           -> QueryExpr          -- ^ query
           -> ShowS
generateZ3 us s query = fcat $ map go uniqueJoinTables
  where
    joinTables = map (nameToCatName.getName) $ extractJoinTables query
    selects = getSelects query

    uniqueJoinTables = nub joinTables

    -- XXX: does not consider nested queries!
    schema = Map.filterWithKey (\k v -> k `elem` uniqueJoinTables) s

    uniqueAsserts fixedTable = fcat [genUnique schema fixedTable tbl cols | (tbl, colss) <- us, cols <- colss]
    whereAsserts fixedTable = fcat $ map (genWhere schema fixedTable) $ extractWhereExpr query
    mkTuple = showString "mk-tuple"
    funDecl = z3DeclareFun mkTuple (map (genType.fst) selects) (showString "Int")
    distinctAsserts fixedTable = let
        (e1s, e2s) = unzip [(e1, e2) | (_, e) <- selects, let e1 : e2 : _ = genScalarExpr' fixedTable e]
      in z3Assert $ z3Distinct [showP $ mkTuple `spaced` sepBySpace e1s, showP $ mkTuple `spaced` sepBySpace e2s]

    getName (Tref _ n) = n -- TODO: obviously...

    go fixedTable = id
      . z3Push
      . genDecls schema fixedTable
      . uniqueAsserts fixedTable
      . whereAsserts fixedTable
      . funDecl
      . distinctAsserts fixedTable
      . z3CheckSat
      . z3Pop

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
  "bool"    -> "Bool"
  "text"    -> "String"
  n'        -> ice $ printf "Invalid type \"%s\"." n'

genNameComponent :: NameComponent -> ShowS
genNameComponent (Nmc s) = showString s
genNameComponent (QNmc s) = showString s
genNameComponent (AntiNameComponent s) = showString s

genCatName :: CatName -> ShowS
genCatName = showString . unpack

genColNamePrefix :: CatName -> CatName -> ShowS
genColNamePrefix tbl row = genCatName tbl . showChar '-' . genCatName row

genColName :: CatName -> CatName -> ShowS -> ShowS
genColName tbl row suffix = genColNamePrefix tbl row . suffix

-- TODO: get rid of duplicates
genWhere :: DbSchema -> CatName -> ScalarExpr -> ShowS
genWhere schema fixed e = z3Assert e1 . z3Assert e2
  where e1 : e2 : _ = genScalarExpr' fixed e

genDecls :: DbSchema -> CatName -> ShowS
genDecls schema fixed = fcat $ concatMap go $ Map.toList schema
  where
    go (tbl, cols)
      | tbl == fixed = map (goFixed tbl) cols
      | otherwise = map (goVariable tbl) cols

    goFixed tbl col = let
        name = genColNamePrefix tbl (fst col)
      in z3DeclareConst name (genType (snd col))

    goVariable tbl col = let
        name1 = genColName tbl (fst col) (showString "-1")
        name2 = genColName tbl (fst col) (showString "-2")
        decl1 = z3DeclareConst name1 (genType (snd col))
        decl2 = z3DeclareConst name2 (genType (snd col))
      in decl1 . decl2

-- ^ Assumes that "tbl" is not the one that is fixed!
genUnique :: DbSchema -> CatName -> Name -> [NameComponent] -> ShowS
genUnique schema fixedTable tbl us
  | tblName == fixedTable = id
  | null otherColNames = id
  | otherwise = z3Assert (precond `z3Impl` postcond)
  where
    tblName = nameToCatName tbl
    usNames = map nameComponentToCatName us
    uniqueColNames = map (genColNamePrefix tblName) usNames
    mk1 x = x . showString "-1"
    mk2 x = x . showString "-2"
    mkEq name = z3Eq (mk1 name) (mk2 name)
    precond = z3And $ map mkEq uniqueColNames
    postcond = z3And $ map mkEq otherColNames

    -- TODO: only own table?
    otherColNames = [genColNamePrefix tbl' col |
        (tbl', cols) <- Map.toList schema,
        fixedTable /= tbl',
        (col, _) <- cols
      ]

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
      _ -> ice "Invalid scalar expression." -- TODO: location