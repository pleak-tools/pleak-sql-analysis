{-# LANGUAGE LambdaCase #-}

module Z3Bridge (
  dbFromCatalogUpdates,
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

z3DeclareConst :: ShowS -> ShowS -> ShowS
z3DeclareConst var ty = showP (showString "declare-const" . space . var . space . ty) . nl

------------------------------------
-- Information about the database --
------------------------------------

-- TODO: move to Schema.hs

type TableInfo = [(CatName, CatName)]
type DbSchema = Map CatName TableInfo

dbTables :: DbSchema -> [CatName]
dbTables = map fst . Map.toList

dbFromCatalogUpdates :: [CatalogUpdate] -> DbSchema
dbFromCatalogUpdates us = Map.fromList [(n, map (second catName) cols) | CatCreateTable (_, n) cols <- us]

---------------------------
-- Generate Z3 statement --
---------------------------

-- TODO: partial
-- ^ Generate Z3 code to verify if query is <= 1 sensitive
generateZ3 :: [[NameComponent]]  -- ^ uniques
           -> [NameComponent]    -- ^ non-nulls
           -> [ScalarExpr]       -- ^ checks
           -> DbSchema           -- ^ information about the database
           -> QueryExpr          -- ^ query
           -> ShowS
generateZ3 _ _ _ schema query =
  fcat $ map go uniqueJoinTables
  where
    joinTables = map (nameToCatName.getName) $ extractJoinTables query

    uniqueJoinTables = nub joinTables

    getName (Tref _ n) = n

    go fixedTable =
      z3Push .
      genDecls schema fixedTable .
      z3CheckSat .
      z3Pop

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

genColNamePrefix :: CatName -> (CatName, CatName) -> ShowS
genColNamePrefix tbl (row, _) = genCatName tbl . showChar '-' . genCatName row

genDecls :: DbSchema -> CatName -> ShowS
genDecls schema fixed = fcat $ concatMap go $ Map.toList schema
  where
    go (tbl, cols)
      | tbl == fixed = map (goFixed tbl) cols
      | otherwise = map (goVariable tbl) cols

    goFixed tbl col = let
        name = genColNamePrefix tbl col
      in z3DeclareConst name (genType (snd col))

    goVariable tbl col = let
        prefix = genColNamePrefix tbl col
        name1 = prefix . showString "-1"
        name2 = prefix . showString "-2"
        decl1 = z3DeclareConst name1 (genType (snd col))
        decl2 = z3DeclareConst name2 (genType (snd col))
      in decl1 . decl2

genUnique :: DbSchema -> Name -> [NameComponent] -> ShowS
genUnique schema tbl us = undefined

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