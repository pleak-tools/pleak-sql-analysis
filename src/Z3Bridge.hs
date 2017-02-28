{-# LANGUAGE LambdaCase #-}

module Z3Bridge (
  dbFromCatalogUpdates,
  dbUniqueInfoFromStatements,
  generateZ3)
  where

import Control.Arrow
import Data.Char
import Data.List
import Data.Map (Map)
import Data.Text (unpack, pack)
import Database.HsSqlPpp.Catalog
import Database.HsSqlPpp.Syntax
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
z3Assert s = showP (showString "assert" . space . s) . nl

z3Eq :: ShowS -> ShowS -> ShowS
z3Eq e1 e2 = showP $ showChar '=' . space . e1 . space . e2

z3And :: [ShowS] -> ShowS
z3And es = showP (showString "and " . fcat (intersperse space es))

z3Impl :: ShowS -> ShowS -> ShowS
z3Impl e1 e2 = showP $ showString "=>" . space . e1 . space . e2

z3DeclareConst :: ShowS -> ShowS -> ShowS
z3DeclareConst var ty = showP (showString "declare-const" . space . var . space . ty) . nl

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

-- TODO: partial
-- ^ Generate Z3 code to verify if query is <= 1 sensitive
generateZ3 :: UniqueInfo         -- ^ uniques
           -> [NameComponent]    -- ^ non-nulls
           -> [ScalarExpr]       -- ^ checks
           -> DbSchema           -- ^ information about the database
           -> QueryExpr          -- ^ query
           -> ShowS
generateZ3 us _ _ schema query =
  fcat $ map go uniqueJoinTables
  where
    joinTables = map (nameToCatName.getName) $ extractJoinTables query

    uniqueJoinTables = nub joinTables

    uniqueAsserts fixedTable = fcat [genUnique schema fixedTable tbl cols | (tbl, colss) <- us, cols <- colss]

    getName (Tref _ n) = n

    go fixedTable =
      z3Push .
      genDecls schema fixedTable .
      uniqueAsserts fixedTable .
      z3CheckSat .
      z3Pop

nameComponentToCatName :: NameComponent -> CatName
nameComponentToCatName n = pack $ genNameComponent n ""

nameToCatName :: Name -> CatName
nameToCatName n = pack $ genName n ""

genName :: Name -> ShowS
genName (AntiName n) = showString n
genName (Name _ ns) = fcat $ intersperse (showString "-") $ map genNameComponent ns

-- TODO: "IS" and "IS NOT" dont work the same way as "=" and "!="
genOp :: Name -> ShowS
genOp n = maybe id (ice errMsg) $ lookup n' ops
  where
    n' = map toLower (genName n "")
    errMsg  = printf "Undefined operator \"%s\"" n'
    ops = map (second showString) [
        ("not", "not"),
        ("||", "or"), ("or", "or"),
        ("&&", "and"), ("and", "and"),
        ("<>", "distinct"), ("!=", "distinct"), ("is not", "distinct"),
        ("*", "*"), ("+", "+"), ("-", "-"), ("/", "/"), ("%", "%")
      ]

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
        prefix = genColNamePrefix tbl (fst col)
        name1 = prefix . showString "-1"
        name2 = prefix . showString "-2"
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

-- TODO: function calls
genScalarExpr :: ScalarExpr -> ShowS
genScalarExpr = \case
  Identifier _ n -> genName n
  NumberLit _ s -> showString s
  BooleanLit _ b -> shows b
  StringLit _ s -> shows s
  Parens _ e -> genScalarExpr e
  PrefixOp _ op e ->
    showP            $
    genOp op         .
    space            .
    genScalarExpr e
  BinaryOp _ op e1 e2 ->
    showP            $
    genOp op         .
    space            .
    genScalarExpr e1 .
    space            .
    genScalarExpr e2
  _ -> ice "Invalid scalar expression." -- TODO: location