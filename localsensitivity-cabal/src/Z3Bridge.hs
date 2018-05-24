{-# LANGUAGE LambdaCase #-}

module Z3Bridge (
  dbFromCatalogUpdates,
  --dbUniqueInfoFromStatements,
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
import Data.Set (Set)
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

--dbUniqueInfoFromStatements :: [Statement] -> UniqueInfo
--dbUniqueInfoFromStatements = map go
--  where
--    go stmt = (extractName stmt, extractUniques stmt)

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

sumGroupsWith :: (Ord a, Ord b) => ([b] -> b) -> [(a,b)] -> [(a,b)]
sumGroupsWith sumf = map (\ g -> (fst (head g), sumf (map snd g))) . groupBy (\ x y -> fst x == fst y) . sort

listGroups :: (Ord a, Ord b) => [(a,b)] -> [(a,[b])]
listGroups = sumGroupsWith concat . map (second (:[]))

nameComponentToCatName :: NameComponent -> CatName
nameComponentToCatName n = pack $ genNameComponent n ""

nameToCatName :: Name -> CatName
nameToCatName n = pack $ genName n ""

genNameComponent :: NameComponent -> ShowS
genNameComponent = showString . ncStr

genName :: Name -> ShowS
genName (AntiName n) = showString n
genName (Name _ ns) = fcat $ intersperse (showString "-") $ map genNameComponent ns

extractTableNames :: [Statement] -> [CatName]
extractTableNames = concatMap extractTableName
  where
    extractTableName (CreateTable _ n _ _ _ _) = [nameToCatName n]
    extractTableName _ = []

