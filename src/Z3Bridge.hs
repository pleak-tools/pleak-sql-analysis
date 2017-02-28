{-# LANGUAGE LambdaCase #-}

module Z3Bridge where

import Control.Arrow
import Data.Char
import Data.List
import Database.HsSqlPpp.Syntax
import Text.Printf

import Logging

-- ^ Generate Z3 code to verify if query is <= 1 sensitive
generateZ3 :: [[NameComponent]]  -- ^ uniques
           -> [NameComponent]    -- ^ non-nulls
           -> [ScalarExpr]       -- ^ checks
           -> QueryExpr          -- ^ query
           -> ShowS
generateZ3 uniques nonnulls es q = undefined

genName :: Name -> ShowS
genName (AntiName n) = showString n
genName (Name _ ns) = foldr (.) id $ intersperse (showString ".") $ map genNameComponent ns

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

genNameComponent :: NameComponent -> ShowS
genNameComponent (Nmc s) = showString s
genNameComponent (QNmc s) = showString s
genNameComponent (AntiNameComponent s) = showString s

-- TODO: function calls
genScalarExpr :: ScalarExpr -> ShowS
genScalarExpr = \case
  Identifier _ n -> genName n
  NumberLit _ s -> showString s
  BooleanLit _ b -> shows b
  Parens _ e -> genScalarExpr e
  PrefixOp _ op e ->
    showString "("   .
    genOp op         .
    genScalarExpr e  .
    showString ")"
  BinaryOp _ op e1 e2 ->
    showString "("   .
    genOp op         .
    genScalarExpr e1 .
    genScalarExpr e2 .
    showString ")"
  _ -> ice "Invalid scalar expression." -- TODO: location