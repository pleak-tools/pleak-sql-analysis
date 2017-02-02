
type Name = String

type TableName = Name

type ColumnName = Name

{-------------------
 - Supported types -
 -------------------}

data SqlType
  = SqlTypeBoolean
  | SqlTypeInteger Integer
  | SqlTypeReal
  | SqlTypeBlob
  | SqlTypeText

{----------------------
 - Column constraints -
 ----------------------}

data ColumnConstraint
  = NotNull
  | Unique

type ColumnConstraints = [ColumnConstraint]

{-----------------------------------------
 - Simplified abstract syntax of queries -
 -----------------------------------------}

-- Note that this is not concrete syntax but simplified abstract syntax.
-- We assume the following:
-- * All columns names have to be qualified with the table name and
--   all results need to be named.
-- * All '*' and 't.*' have been properly expanded.
-- * Results of SELECT are explicitly named.
-- * Everything here is well typed.
-- * No implicit type conversions.
-- * Resulting names in the FROM clause must be unique.
--
-- TODO:
-- * location information
-- * type information
-- * more general GROUP BY (currently only groups by some subset of columns)

data SelectQuery = SelectQuery {            -- select-query ::=
    selColumns    :: [NamedExpr],           --   SELECT (e AS c)*
    selFrom       :: [NamedTable],          --     FROM (t AS t')*
    selWhere      :: Maybe ScalarExpr,      --     WHERE e?
    selGroupBy    :: [ColumnRef]            --     GROUP BY (t.c)*
  }

-- Small examples.
--
-- 1. sum the entire "value" column of "table"
--
-- SelectQuery
--    [exprSum (mkCol "table" "value") `named` "sum"]
--    [mkDefaultNamedTable "table"]
--    Nothing
--    []
--
-- 2. identity
--
-- SelectQuery
--    [mkCol "table" "key" `named` "key", mkCol "table" "value" `named` "value"]
--    [mkDefaultNamedTable "table"]
--    Nothing
--    []
--
-- 3. select distrinct values from key value table
--
-- SelectQuery
--    [mkCol "table" "value" `named` "value"]
--    [mkDefaultNamedTable "table"]
--    Nothing
--    ["table" `ColumnRef` "value"]

data NamedTable
  = NamedTable TableName TableName

mkDefaultNamedTable :: TableName -> NamedTable
mkDefaultNamedTable t = NamedTable t t

data NamedExpr
  = NamedExpr ScalarExpr ColumnName

named :: ScalarExpr -> ColumnName -> NamedExpr
named = NamedExpr

data ColumnRef = ColumnRef TableName ColumnName

type ScalarExpr = Expr

data Expr
  = ExprLit LiteralValue
  | ExprCol ColumnRef
  | ExprUnary UnaryOp Expr
  | ExprBinary BinaryOp Expr Expr
  | ExprAggregate AggregateOp Expr

exprSum :: Expr -> Expr
exprSum = ExprAggregate SumOp

data LiteralValue
  = LitNull
  | LitInt Integer
  | LitBool Bool

data UnaryOp
  = NotOp
  | NegOp

data BinaryOp
  = LtOp
  | GtOp
  | LeOp
  | GeOp
  | EqOp
  | NeOp
  | IsOp
  | IsNotOp
  | OrOp
  | AndOp

data AggregateOp
  = SumOp
  | AvgOp
  | MinOp
  | MaxOp
  | CountOp
