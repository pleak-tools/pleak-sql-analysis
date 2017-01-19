
type Name = String

type TableName = Name

type ColumnName = Name

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

data SelectQuery = SelectQuery {            -- select-query ::=
    selColumns    :: [ResultColumn],        --   SELECT (e AS name)*
    selFrom       :: [NamedTable],          --     FROM (name AS name')*
    selWhere      :: Maybe ScalarExpr,      --     WHERE e?
    selGroupBy    :: [TableName]            --     GROUP BY name*
  }

data NamedTable
  = NamedTable TableName TableName

mkDefaultNamedTable :: TableName -> NamedTable
mkDefaultNamedTable t = NamedTable t t

data ResultColumn
  = ResultColumn ScalarExpr ColumnName

type ScalarExpr = Expr

data Expr
  = ExprLit LiteralValue
  | ExprCol TableName ColumnName
  | ExprUnary UnaryOp Expr
  | ExprBinary BinaryOp Expr Expr
  | ExprAggregate AggregateOp Expr

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
