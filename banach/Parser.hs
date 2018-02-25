module Parser where

import System.Environment
import System.IO.Unsafe

-- some Megaparsec-specific modules
import Text.Megaparsec
import Text.Megaparsec.Expr
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
--
import qualified Control.Exception as Exc
import Control.Monad (void,when)
import Debug.Trace

import Data.Bits
import Data.Char
import Data.Either
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Void

-- import Expr directly from Banach.hs, 'qualified' because we want to reuse the names
import qualified Banach as B
import Aexpr
import ErrorMsg
import Expr
import Norms
import Query

-- Define the parser type
-- 'Void' means 'no custom error messages'
-- 'String' means 'input comes in form of a String'
type Parser = Parsec Void String

type TableName  = String
type TableAlias = String

-- a small bit, denoting whether we are parsing a query or a norm
-- we define it, since a query and a norm have very similar format
data ParserInstance = QueryParsing | NormParsing

---------------------------------------------------------------------------------------------
-- TODO: parsing of 'expr' and 'tableExpr' is being synchronized with B.Expr and B.TableExpr

-- keywords
allKeyWords :: S.Set String -- set of reserved "words"
allKeyWords = S.fromList ["return",
               "const","^","LN","exp","sqrt","root","scaleNorm","zeroSens","lp","linf","prod","inv","div","min","max","sigmoid","tauoid",
               "selectMin","selectMax","selectProd","selectL"]

allCaseInsensKeyWords :: S.Set String -- set of reserved "words"
allCaseInsensKeyWords = S.fromList ["select","as","from","where","and","min","max","sum","product","count","distinct","group","by","between"]

-- a query expression
queryExpr :: VarName -> Parser [Expr]
queryExpr x = powerExpr
  <|> powerLNExpr
  <|> invExpr
  <|> divExpr x
  <|> expExpr
  <|> scaleNormExpr
  <|> zeroSensExpr
  <|> lpNormExpr
  <|> linfNormExpr
  <|> prodExpr
  <|> minExpr
  <|> maxExpr
  <|> sigmoidExpr
  <|> tauoidExpr
  <|> sumpExpr
  <|> sumInfExpr
  <|> constExpr

-- a norm expression
normExpr :: VarName -> Parser [Expr]
normExpr _ = scaleNormExpr
  <|> zeroSensExpr
  <|> lpNormExpr
  <|> linfNormExpr
  <|> lnExpr

-- parsing different expressions, one by one
constExpr :: Parser [Expr]
constExpr = do
  keyWord "const"
  b <- signedFloat
  return [Const b]

powerExpr :: Parser [Expr]
powerExpr = do
  keyWord "^"
  a <- varName
  b <- float
  return [Power a b]

powerLNExpr :: Parser [Expr]
powerLNExpr = do
  keyWord "LN"
  keyWord "^"
  a <- varName
  b <- signedFloat
  return [PowerLN a b]

invExpr :: Parser [Expr]
invExpr = do
  keyWord "inv"
  a <- varName
  let b = -1.0
  return [PowerLN a b]

divExpr ::  VarName -> Parser [Expr]
divExpr x = do
  keyWord "div"
  a <- varName
  b <- varName
  let c = -1.0
  return [Prod [a,x ++ "~1"], PowerLN b c]

expExpr :: Parser [Expr]
expExpr = do
  keyWord "exp"
  a <- signedFloat
  b <- varName
  return [Exp a b]

scaleNormExpr :: Parser [Expr]
scaleNormExpr = do
  keyWord "scaleNorm"
  a <- float
  b <- varName
  return [ScaleNorm a b]

zeroSensExpr :: Parser [Expr]
zeroSensExpr = do
  keyWord "zeroSens"
  a <- varName
  return [ZeroSens a]

lpNormExpr :: Parser [Expr]
lpNormExpr = do
  keyWord "lp"
  a  <- float
  bs <- many varName
  return [L a bs]

linfNormExpr :: Parser [Expr]
linfNormExpr = do
  keyWord "linf"
  bs <- many varName
  return [LInf bs]

prodExpr :: Parser [Expr]
prodExpr = do
  keyWord "prod"
  bs <- many varName
  return [Prod bs]

minExpr :: Parser [Expr]
minExpr = do
  keyWord "min"
  bs <- many varName
  return [Min bs]

maxExpr :: Parser [Expr]
maxExpr = do
  keyWord "max"
  bs <- many varName
  return [Max bs]

sigmoidExpr :: Parser [Expr]
sigmoidExpr = do
  keyWord "sigmoid"
  a <- float
  c <- float
  x <- varName
  return [Sigmoid a c x]

tauoidExpr :: Parser [Expr]
tauoidExpr = do
  keyWord "tauoid"
  a <- float
  c <- float
  x <- varName
  return [Tauoid a c x]

sumpExpr :: Parser [Expr]
sumpExpr = do
  keyWord "sump"
  c <- float
  bs <- many varName
  return [Sump c bs]

sumInfExpr :: Parser [Expr]
sumInfExpr = do
  keyWord "sumInf"
  bs <- many varName
  return [SumInf bs]

-- this one is intended only for norms
lnExpr :: Parser [Expr]
lnExpr = do
  keyWord "LN"
  a <- varName
  return [PowerLN a 0.0]

-- a table expression
queryTableExpr :: Parser TableExpr
queryTableExpr = selectProdExpr
  <|> selectMinExpr
  <|> selectMaxExpr
  <|> selectLExpr
  <|> selectSumpExpr
  <|> selectSumInfExpr

-- a table expression for norms (which norm is applied to the rows)
normTableExpr :: Parser TableExpr
normTableExpr = selectProdExpr
  <|> linfTableExpr
  <|> lpTableExpr

-- parsing different expressions, one by one
selectProdExpr :: Parser TableExpr
selectProdExpr = do
  keyWord "selectProd"
  a <- varName
  return (SelectProd a)

selectMinExpr :: Parser TableExpr
selectMinExpr = do
  keyWord "selectMin"
  a <- varName
  return (SelectMin a)

selectMaxExpr :: Parser TableExpr
selectMaxExpr = do
  keyWord "selectMax"
  a <- varName
  return (SelectMax a)

selectLExpr :: Parser TableExpr
selectLExpr = do
  keyWord "selectL"
  c <- float
  a <- varName
  return (SelectL c a)

selectSumpExpr :: Parser TableExpr
selectSumpExpr = do
  keyWord "selectSump"
  c <- float
  a <- varName
  return (SelectSump c a)

selectSumInfExpr :: Parser TableExpr
selectSumInfExpr = do
  keyWord "selectSumInf"
  a <- varName
  return (SelectSumInf a)

lpTableExpr :: Parser TableExpr
lpTableExpr = do
  keyWord "lp"
  a <- float
  b <- varName
  return (SelectL a b)

linfTableExpr :: Parser TableExpr
linfTableExpr = do
  keyWord "linf"
  b <- varName
  return (SelectMax b)

------------------------------------------------
-- Parsing a function as a complex expression --
------------------------------------------------

-- arithmetic expressions
powerAExpr :: Parser (AExpr a -> AExpr a)
powerAExpr = do
  keyWord "^"
  a <- signedFloat
  return (AUnary (APower a))

sqrtAExpr :: Parser (AExpr a -> AExpr a)
sqrtAExpr = do
  keyWord "sqrt"
  return (AUnary (ARoot 2.0))

rootAExpr :: Parser (AExpr a -> AExpr a)
rootAExpr = do
  keyWord "root"
  r <- float
  return (AUnary (ARoot r))

lnAExpr :: Parser (AExpr a -> AExpr a)
lnAExpr = do
  keyWord "ln"
  return (AUnary ALn)

expAExpr :: Parser (AExpr a -> AExpr a)
expAExpr = do
  keyWord "exp"
  r <- signedFloat
  return (AUnary (AExp r))

-- TODO this could probably be improved, but there are no circumfix operators
absBeginAExpr :: Parser (AExpr a -> AExpr a)
absBeginAExpr = do
  symbol "|"
  return (AUnary AAbsBegin)

absEndAExpr :: Parser (AExpr a -> AExpr a)
absEndAExpr = do
  symbol "|"
  return (AUnary AAbsEnd)

aExpr :: Parser (AExpr VarName)
aExpr = makeExprParser aTerm aOperators

namedAExpr :: Parser (VarName, VarName -> TableExpr, AExpr VarName)
namedAExpr = do
    g <- sqlAggregator
    aexpr <- aExpr
    caseInsensKeyWord "as"
    newColName <- varName
    return (newColName, g, aexpr)

unnamedAExpr :: Parser (VarName -> TableExpr, AExpr VarName)
unnamedAExpr = do
    g <- sqlAggregator
    aexpr <- aExpr
    return (g, aexpr)

aOperators :: [[Operator Parser (AExpr a)]]
aOperators =
  [ [ Prefix  absBeginAExpr
    , Postfix absEndAExpr]

  , [ Prefix lnAExpr
    , Prefix expAExpr]
  , [ Prefix sqrtAExpr
    , Prefix rootAExpr
    , Postfix powerAExpr]

  , [ InfixL (ABinary AMult <$ symbol "*")
    , InfixL (ABinary ADiv  <$ symbol "/") ]

  , [ InfixL (ABinary AAdd <$ symbol "+")
    , InfixL (ABinary ASub <$ symbol "-") ]
  ]

aTerm :: Parser (AExpr VarName)
aTerm = parens aExpr
  <|> AVar <$> varName
  <|> AConst <$> signedFloat
  <|> aDummy

aDummy = do
  symbol "*"
  return (AConst 0.0)


------------------------------------------------------------
---- Parsing SQL query (simlpified, could be delegated) ----
------------------------------------------------------------
order :: Parser Ordering
order = ordLE <|> ordLT <|> ordEQ <|> ordGE <|> ordGT
ordLT = do
  symbol "<"
  return LT
ordLE = do
  symbol "<="
  return LT
ordEQ = do
  symbol "==" <|> symbol "="
  return EQ
ordGT = do
  symbol ">"
  return GT
ordGE = do
  symbol ">="
  return GT

sqlAggregator :: Parser (VarName -> TableExpr)
sqlAggregator = selectProdAExpr
  <|> selectMinAExpr
  <|> selectMaxAExpr
  <|> selectSumAExpr
  <|> selectCountAExpr
  <|> selectDistinctAExpr
  <|> selectAExpr

selectProdAExpr :: Parser (VarName -> TableExpr)
selectProdAExpr = do
  caseInsensKeyWord "product"
  return SelectProd

selectMinAExpr :: Parser (VarName -> TableExpr)
selectMinAExpr = do
  caseInsensKeyWord "min"
  return SelectMin

selectMaxAExpr :: Parser (VarName -> TableExpr)
selectMaxAExpr = do
  caseInsensKeyWord "max"
  return SelectMax

selectSumAExpr :: Parser (VarName -> TableExpr)
selectSumAExpr = do
  caseInsensKeyWord "sum"
  return SelectSum

selectCountAExpr :: Parser (VarName -> TableExpr)
selectCountAExpr = do
  caseInsensKeyWord "count"
  return SelectCount

selectDistinctAExpr :: Parser (VarName -> TableExpr)
selectDistinctAExpr = do
  caseInsensKeyWord "distinct"
  return SelectDistinct

selectAExpr :: Parser (VarName -> TableExpr)
selectAExpr = do
  return Select

filterVarConst :: Parser [Function]
filterVarConst = do
  aexpr <- aExpr
  op <- order
  c <- signedFloat
  let y = "filt~"
  let as = aexprToExpr y (aexprNormalize $ aexpr)
  let b  = Filt op y c
  return [F as b]

filterVarVar :: Parser [Function]
filterVarVar = do
  aexpr1 <- aExpr
  op <- order
  aexpr2 <- aExpr
  let y  = "filt~"
  let y1 = "filty1~"
  let y2 = "filty2~"
  let z1 = "filtz1~"
  let z2 = "filtz2~"

  let as1 = M.toList $ aexprToExpr y1 (aexprNormalize $ aexpr1)
  let as2 = M.toList $ aexprToExpr y2 (aexprNormalize $ aexpr2)

  let as = M.fromList (as1 ++ as2 ++ [(y, Sum [y1, z2]),(z2, Prod [y2,z1]),(z1, Const (-1.0))])
  let b  = Filt op y 0.0
  return [F as b]

filterBetween :: Parser [Function]
filterBetween = do
  aexpr   <- aExpr
  caseInsensKeyWord "between"
  aexprLB <- aExpr
  caseInsensKeyWord "and"
  aexprUB <- aExpr

  let y  = "filt~"
  let y1 = "filty1~"
  let y2 = "filty2~"
  let z1 = "filtz1~"
  let z2 = "filtz2~"

  let as1   = M.toList $ aexprToExpr y1 (aexprNormalize $ aexpr)
  let asLB2 = M.toList $ aexprToExpr y2 (aexprNormalize $ aexprLB)
  let asUB2 = M.toList $ aexprToExpr y2 (aexprNormalize $ aexprUB)

  let asLB  = M.fromList (as1 ++ asLB2 ++ [(y, Sum [y1, z2]),(z2, Prod [y2,z1]),(z1, Const (-1.0))])
  let asUB  = M.fromList (as1 ++ asUB2 ++ [(y, Sum [y1, z2]),(z2, Prod [y2,z1]),(z1, Const (-1.0))])

  let bLB  = Filt GT y 0.0
  let bUB  = Filt LT y 0.0
  return [F asLB bLB, F asUB bUB]

-- ======================================================================= --
-----------------------------------------------------------------------------
----      The code below does not need to be updated with Banach.hs      ----
-----------------------------------------------------------------------------
sqlFilter :: Parser [Function]
sqlFilter = try filterBetween <|> try filterVarConst <|> filterVarVar

sqlQueries :: Parser [Query]
sqlQueries = try sqlManyQueries <|> sqlOneQuery

sqlManyQueries :: Parser [Query]
sqlManyQueries = do
    qs1 <- many sqlAsgnQuery
    qs2  <- sqlAggrQuery
    return $ (concat qs1) ++ qs2

sqlOneQuery :: Parser [Query]
sqlOneQuery = do
    qs  <- sqlAggrQuery
    return qs

sqlAsgnQuery :: Parser [Query]
sqlAsgnQuery = do
  tableName <- tableName
  void (asgn)
  (gs,colNames,groups,aexprs,tableNames,tableAliases,filters,internalQueries) <- sqlQuery
  -- let fs = zipWith3 (\g x y -> F (aexprToExpr (tableName ++ "." ++ y) $ aexprNormalize x) (g (tableName ++ "." ++ y))) gs aexprs colNames
  let fs = zipWith3 (\g x y -> F (aexprToExpr y $ aexprNormalize x) (g y)) gs aexprs colNames
  let tableAliasMap = M.fromList $ zip tableAliases tableNames
  let subquery = P tableName colNames groups fs tableAliasMap filters
  return $ internalQueries ++ [subquery]

sqlQuery :: Parser ([VarName -> TableExpr],[VarName],[VarName],[AExpr VarName],[TableName],[TableAlias],[Function],[Query])
sqlQuery = do
  caseInsensKeyWord "select"
  namedAExprs <- sepBy1 namedAExpr (symbol ",")
  let (names, gs, aexprs) = unzip3 namedAExprs

  caseInsensKeyWord "from"
  internalTableData <- sepBy1 internalTable (symbol ",")
  let (tableNames,tableAliases,internalQueries) = unzip3 internalTableData
  filters <- sqlQueryFilter
  groups  <- sqlQueryGroupBy

  return (gs,names,groups,aexprs,tableNames,tableAliases,filters,concat internalQueries)

sqlAggrQuery :: Parser [Query]
sqlAggrQuery = do
  caseInsensKeyWord "select"
  unnamedAExprs <- sepBy1 unnamedAExpr (symbol ",")
  let (gs, aexprs) = unzip unnamedAExprs

  caseInsensKeyWord "from"
  internalTableData <- sepBy1 internalTable (symbol ",")
  let (tableNames,tableAliases,internalQueries) = unzip3 internalTableData
  filters <- sqlQueryFilter
  groups  <- sqlQueryGroupBy

  let ys = map (\i -> "y~" ++ show i) [0..length gs - 1]
  let queryFuns = zipWith3 (\g aexpr y -> F (aexprToExpr y (aexprNormalize $ aexpr)) (g y)) gs aexprs ys
  let tableAliasMap = M.fromList $ zip tableAliases tableNames
  let subquery = P "output" [] groups queryFuns tableAliasMap filters
  return $ (concat internalQueries) ++ [subquery]

internalTable :: Parser (TableName, TableAlias, [Query])
internalTable = internalTableQuery <|> try internalTableNameAS <|> internalTableName 

-- give the table name and the alias explicitly
internalTableNameAS = do
    tableName <- identifier
    caseInsensKeyWord "as"
    tableAlias <- identifier
    return (tableName, tableAlias, [])

-- the real name of a nested query equals the alias, and we know that there cannot be multiple copies of it
internalTableQuery = do
    (gs,colNames,groups,aexprs,tableNames,tableAliases,filters,internalQueries) <- parens sqlQuery
    caseInsensKeyWord "as"
    tableAlias <- identifier
    --let fs = zipWith3 (\g x y -> F (aexprToExpr (tableAlias ++ "." ++ y) $ aexprNormalize x) (g (tableAlias ++ "." ++ y))) gs aexprs colNames
    let fs = zipWith3 (\g x y -> F (aexprToExpr y $ aexprNormalize x) (g y)) gs aexprs colNames
    let tableAliasMap = M.fromList $ zip tableAliases tableNames
    let subquery = P tableAlias colNames groups fs tableAliasMap filters
    return (tableAlias, tableAlias, internalQueries ++ [subquery])

-- if an alias is not specified, then the table name is used directly
internalTableName = do
    tableName <- identifier
    return (tableName, tableName, [])

sqlQueryFilter :: Parser [Function]
sqlQueryFilter = sqlQueryWithFilter <|> sqlQueryWithoutFilter

sqlQueryWithoutFilter :: Parser [Function]
sqlQueryWithoutFilter = do
  return []

sqlQueryWithFilter :: Parser [Function]
sqlQueryWithFilter = do
  caseInsensKeyWord "where"
  filters <- sepBy1 sqlFilter (caseInsensKeyWord "and")
  return (concat $ filters)

sqlQueryGroupBy :: Parser [String]
sqlQueryGroupBy = sqlQueryWithGroupBy <|> sqlQueryWithoutGroupBy

sqlQueryWithoutGroupBy :: Parser [String]
sqlQueryWithoutGroupBy = do
  return []

sqlQueryWithGroupBy :: Parser [String]
sqlQueryWithGroupBy = do
  caseInsensKeyWord "group"
  caseInsensKeyWord "by"
  colnames <- sepBy1 identifier (symbol ",")
  return colnames

--------------------------------------
---- Parsing general input format ----
--------------------------------------
query :: Parser Query
query = do
  tablePath <- text
  void (delim)
  xs <- many varName
  void (delim)
  f <- function QueryParsing
  let tableAliasMap = M.fromList [(tablePath,tablePath)]
  return $ P "output" [] [] [f] tableAliasMap []

-- the first row in the norm file is the list of sensitive rows
-- the second row in the norm file is the list of sensitive columns
norm :: Parser (([Int], [VarName]), Function)
norm = do
  is <- many integer
  xs <- many varName
  void (delim)
  f <- try customNorm <|> defaultNorm xs
  return ((is, xs), f)

customNorm = do
  f <- function NormParsing
  return f

defaultNorm xs = do
  let f = F (M.fromList [("z",L 1.0 xs)]) (SelectMax "z")
  return f

asgnStmt :: ParserInstance -> Parser [(VarName,Expr)]
asgnStmt p = do
  a  <- varName
  void (asgn)
  bs <- case p of {QueryParsing -> queryExpr a; NormParsing -> normExpr a}
  -- this introduces new temporary variables for complex expressions 
  -- here "~" can be any symbol that is not allowed to use in variable names
  let as = map (\x -> a ++ "~" ++ show x) [1 .. length bs - 1]
  void (delim)
  return (zip (a:as) bs)

returnStmt :: ParserInstance -> Parser TableExpr
returnStmt p = do
  keyWord "return"
  a <- case p of {QueryParsing -> queryTableExpr; NormParsing -> normTableExpr}
  void (delim)
  return a

function :: ParserInstance -> Parser Function
function p = do
  ass <- many (asgnStmt p)
  b  <- returnStmt p
  let as = concat ass
  return (F (M.fromList as) b)


------------------------------
---- Symbols and keywords ----
------------------------------

-- delimiter of rows
delim :: Parser String
delim = symbol ";"

-- assignment symbol
asgn :: Parser String
asgn = symbol "="

-- line comment
lineComment :: String
lineComment = "//"

-- block comment
blockCommentStart :: String
blockCommentStart = "/*"

blockCommentEnd :: String
blockCommentEnd = "*/"

-------------------------------------
---- Some auxiliary subparsers   ----
-------------------------------------

-- this is to extract the actual parsed data
-- seems very ugly, there should be some easier way to extract data from "Either"
parseData :: (Parser a) -> (String -> String) -> String -> a
parseData p err s = 
    let res = parse p "" s in
    case res of
        Left  x -> error $ err (parseErrorPretty x)
        Right x -> x

parseFromFile :: (Parser a) -> (String -> String -> String) -> String -> IO a
parseFromFile p err s = fmap (parseData p (err s)) (readInput s)

parseTestFromFile :: (Show a, ShowErrorComponent e) => Parsec e String a -> FilePath -> IO ()
parseTestFromFile p s = parseTest p (unsafePerformIO (readInput s))

parseNormFromFile fileName = parseFromFile norm error_parseNorm fileName
parseQueryFromFile fileName = parseFromFile query error_parseQuery fileName
parseSqlQueryFromFile fileName = parseFromFile sqlQueries error_parseSqlQuery fileName

-- a keyword
keyWord :: String -> Parser ()
keyWord w = lexeme (C.string w *> notFollowedBy C.alphaNumChar)

caseInsensKeyWord :: String -> Parser ()
caseInsensKeyWord w = lexeme (C.string' w *> notFollowedBy C.alphaNumChar)

-- variable identifier, as taken from the tutorial
-- it checks that the identifier is not a keyword
identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p       = (:) <$> C.letterChar <*> many alphaNumCharAndPeriod
    check x = if S.member (map toLower x) allCaseInsensKeyWords || S.member x allKeyWords
              then fail $ "keyword " ++ show x ++ " cannot be an identifier"
              else return x

alphaNumCharAndPeriod :: Parser Char
alphaNumCharAndPeriod = C.char '.'
    <|> C.char '_'
    <|> C.alphaNumChar

-- we need to read string identifiers and afterwards map them to integers
varName :: Parser VarName
varName = identifier

tableName :: Parser TableName
tableName = identifier

tableAlias :: Parser TableAlias
tableAlias = identifier

constant :: Parser VarName
constant = do
    c <- signedFloat
    return ("const" ++ show c)

--reads an arbitrary string, all characters up to the first space
text :: Parser String
text = lexeme (C.char '"' >> manyTill L.charLiteral (C.char '"'))

-- this thing eats all spaces and comments
spaceConsumer :: Parser ()
spaceConsumer = 
        L.space C.space1 lineCmnt blockCmnt
    where
        lineCmnt  = L.skipLineComment lineComment
        blockCmnt = L.skipBlockComment blockCommentStart blockCommentEnd

-- reads a lexeme and removes all trailing whitespaces and comments
lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

-- reads a pure string and removes all trailing whitespaces and comments
symbol :: String -> Parser String
symbol = L.symbol spaceConsumer

-- reads an integer
integer :: Parser Int
integer = lexeme L.decimal

-- reads a double
float :: Parser Double
float = try (lexeme L.float) <|> fmap fromIntegral integer

-- reads a signed double
signedFloat :: Parser Double
signedFloat = try (L.signed spaceConsumer float) <|> fmap fromIntegral (L.signed spaceConsumer integer)

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")


-------------------------------------------------------
---- Converting a Query to Banach Analyser input   ----
-------------------------------------------------------

-- read the database from the file as a matrix of doubles
-- read is as a single table row
readDB :: String -> IO ([VarName], B.Table)
readDB dbFileName = do
    (firstLine:ls) <- fmap lines (readInput dbFileName)
    let varNames = words firstLine
    let table    = readDoubles (foldr (\x y -> x ++ "\n" ++ y) "" ls)
    return (varNames, table)


-- the format of the query
--   TableName         is the name of the resulting table
--   "[String]"         is the list of names assigned to the resulting columns
--   "[String]"         is the list of columns by which the result should be grouped
--   "[Function]"       is the list of the queried function itself (SELECT x)
--   "[TableName]"      is the list of input tables that are used in the query (FROM x)
--   "[TableAlias]"     is the list of table names that are used in the query (FROM ... AS x)
--   "[Function]"       is the list of filters used in the query (WHERE x)
data Query
  = P TableName [String] [String] [Function] (M.Map TableAlias TableName) [Function]
  deriving (Show)

getQueryName        (P x _ _ _ _ _) = x
getQueryColNames    (P _ x _ _ _ _) = x
getQueryGroupNames  (P _ _ x _ _ _) = x
getQueryFunctions   (P _ _ _ x _ _) = x
getQueryAliasMap    (P _ _ _ _ x _) = x
getQueryFilters     (P _ _ _ _ _ x) = x


query2Expr :: (M.Map VarName B.Var) -> Function -> (S.Set B.Var, B.Expr)
query2Expr inputMap (F asgnMap y) =
    let x = extractArg y in
    matchAsgnVariable "" queryExpression inputMap asgnMap x

queryExprAggregate :: Function-> B.Expr -> B.TableExpr
queryExprAggregate (F _ y) z =
    queryArg y [z]

queryExprAggregateSensRows :: Int -> [Bool] -> Function-> B.Expr -> B.TableExpr
queryExprAggregateSensRows numOfRows sensitiveRowsCV  (F _ y) z = 
    let zs = zipWith (\x y -> if x then y else B.ZeroSens y) sensitiveRowsCV (replicate numOfRows z) in
    queryArg y zs

norm2Expr :: (Show a, Ord a) => String -> (M.Map VarName a) -> Function -> (Norm a, ADouble)
norm2Expr prefix inputMap (F asgnMap y) =
    let x = extractArg y in
    let (_,z) = matchAsgnVariable prefix normExpression inputMap asgnMap x in
    (z, normArg y)

processExpression :: (Show a, Ord a) => 
                     String ->                                 -- the name of the database file that we prepend to all variable names
                     (Expr -> [a] -> [b] -> [S.Set a] -> b) -> -- the function that actually rewrites the term
                     (M.Map VarName a) ->                        -- input variable map
                     (M.Map VarName Expr) ->                     -- assigmnent variable map
                     Expr ->                                   -- the expression that we rewrite
                     (S.Set a, b)
processExpression s f inputMap asgnMap expr =
    let varNames = extractArgs expr in
    let usedInputVarNames = filter (\x -> M.member (s ++ x) inputMap) varNames in
    let usedAsgnVarNames  = filter (\x -> M.member x asgnMap)  varNames in


    let inputVars        = map (\x -> inputMap ! (s ++ x))                                    usedInputVarNames in
    let asgnInputsExprs  = map (matchAsgnVariable s f inputMap asgnMap) usedAsgnVarNames in

    let (asgnInputs,asgnExprs) = unzip asgnInputsExprs in
    (S.union (S.fromList inputVars) (foldr S.union S.empty asgnInputs), f expr inputVars asgnExprs asgnInputs)

--check if the variable is a keys in a map, apply processExpression to the value of that key
matchAsgnVariable :: (Show a, Ord a) => String -> (Expr -> [a] -> [b] -> [S.Set a] -> b) -> (M.Map VarName a) -> (M.Map VarName Expr) -> VarName -> (S.Set a,b)
matchAsgnVariable s f inputMap asgnMap x =

        -- if y is an assignment variable, find its value recursively
        let expr = (asgnMap ! x) in
        processExpression s f inputMap asgnMap expr

-- read the DB line by line -- no speacial parsing, assume that the delimiters are whitespaces
readInput :: String -> IO String
readInput path = do
   content <- readFile path
   return content

readEither :: (Read a) => String -> Either a String
readEither s = case reads s of
              [(x, "")] -> Left x
              _ -> Right s

-- djb2 hash
hash :: String -> Double
hash = fromIntegral . foldl' (\h c -> xor (33*h) (ord c)) 5381

-- tries to read an integer, then a boolean, and if fails, returns the hash of the input string
readIntBoolString :: String -> Double
readIntBoolString s =
    let a = readEither s :: Either Double String in
    case a of
        Left  x -> x
        Right x ->
            let b = readEither s :: Either Bool String in
            case b of
                Left  x -> fromIntegral $ fromEnum x
                Right x -> hash s

readDoubles :: String -> [[Double]]
readDoubles s = fmap (map readIntBoolString . words) (lines s)

-- add the entire second argument to each query of the first argument list
mergeQueryFuns :: TableAlias -> [Function] -> [(TableAlias, TableName)] -> [Function] -> [Function]
mergeQueryFuns _ [] _ _ = []
mergeQueryFuns prefix (F as b : qs1) subst qs2 =
    let as1 = foldl M.union M.empty $ concat $ map (\(F as' _) -> map (updateVariableNames prefix as') subst) qs2 in
    (F (M.union as as1) b) : (mergeQueryFuns prefix qs1 subst qs2)

updateVariableNames :: TableAlias -> (M.Map VarName Expr) -> (TableAlias, TableName) -> (M.Map VarName Expr)
updateVariableNames prefix as subst =
    let as' = M.mapKeys (updatePrefices prefix subst) as in
    M.map (updatePreficesExpr prefix subst) as'

-- this checks that the subqueries are all of select-type
badQFuns :: [Function] -> (Bool, String)
badQFuns [] = (False,"")
badQFuns (F _ b : qs) =
    case b of
        Select _ -> badQFuns qs
        _        -> (True, error_queryExpr_aggrInterm b)

fillMissingWith :: Int -> Int -> [Int] -> [Int]
fillMissingWith y n xs  = fillMissingWithRec xs y n 0

fillMissingWithRec [] y n i = replicate (n-i) y
fillMissingWithRec (x:xs) y n i =
    if (i == n) then []
    else if (x == i) then x : fillMissingWithRec xs y  n(i+1)
    else if (x > i) then y : fillMissingWithRec (x:xs) y n (i+1)
    else error $ error_internal_fillMissing x i xs

-- compute table data for a cross product
getTableCrossProductData :: [TableAlias] -> M.Map TableAlias TableData -> (B.Table, [VarName], [(TableAlias, Function)], [[Int]], [VarName])
getTableCrossProductData tableAliases tableMap =

    let allInputVars     = map (getColNames .      (tableMap ! ) ) tableAliases in
    let allTables        = map (getTableValues .   (tableMap ! ) ) tableAliases in
    let allExprs         = map (getExpr .          (tableMap ! ) ) tableAliases in
    let allQFuns         = map (getQFun .          (tableMap ! ) ) tableAliases in
    let allNorms         = map (getNorm .          (tableMap ! ) ) tableAliases in
    let allSensitiveRows = map (getSensitiveRows . (tableMap ! ) ) tableAliases in
    let allSensitiveVars = map (getSensitiveCols . (tableMap ! ) ) tableAliases in

    -- the input variables are concatenated in the order of tables, since each of them describes a column
    let inputVarList     = concat allInputVars in
    let normList         = concat allNorms in
    let sensitiveVarList = concat allSensitiveVars in

    -- find the cross product of all used tables
    let crossProductTable = tableJoin allTables in

    -- find the cross product of table row indices to remeber which row has come from which table
    let sensitiveRowCrossProduct = vectorJoin allSensitiveRows in

    (crossProductTable, inputVarList, normList, sensitiveRowCrossProduct, sensitiveVarList)


data TableData =
    -- content columnNames exprs norms aggrNorms sensRows sensCols originalTablename 
    T B.Table [VarName] [B.Expr] [Function] [(TableAlias,Function)] [[Int]] [VarName] TableName
  deriving Show

getTableValues   (T x _ _ _ _ _ _ _) = x 
getColNames      (T _ x _ _ _ _ _ _) = x 
getExpr          (T _ _ x _ _ _ _ _) = x 
getQFun          (T _ _ _ x _ _ _ _) = x 
getNorm          (T _ _ _ _ x _ _ _) = x
getSensitiveRows (T _ _ _ _ _ x _ _) = x 
getSensitiveCols (T _ _ _ _ _ _ x _) = x 
getTableName     (T _ _ _ _ _ _ _ x) = x 
getNumOfCols     (T _ x _ _ _ _ _ _) = length x

readAllTables :: Bool -> [TableName] -> [TableAlias] -> IO (M.Map TableAlias TableData)
readAllTables usePrefices tableNames tableAliases = do

    -- collect all tables and all column names that will be used in our query
    -- read table sensitivities from corresponding files
    -- mapM is a standard function [IO a] -> IO [a]
    let dbData     = mapM (\tableName -> readDB            $ tableName ++ ".db")  tableNames
    let dbNormData = mapM (\tableName -> parseNormFromFile $ tableName ++ ".nrm") tableNames

    (tableColNames,  tableValues)   <- fmap unzip dbData
    (tableSensitives,tableNormFuns) <- fmap unzip dbNormData
    let (tableSensitiveRows,tableSensitiveVars) = unzip tableSensitives

    -- we put table names in front of column names
    let namePrefices = map (\tableAlias -> if usePrefices then tableAlias ++ "." else "") tableAliases
    let taggedTableColNames = zipWith (\x ys -> map (\y -> x ++ y) ys) namePrefices tableColNames
    let taggedSensitiveVars = zipWith (\x ys -> map (\y -> x ++ y) ys) namePrefices tableSensitiveVars

    -- put all table data together
    let tableMap = processAllTables tableAliases tableNames taggedTableColNames tableValues tableNormFuns taggedSensitiveVars tableSensitiveRows
    return (M.fromList tableMap)

processAllTables :: [TableAlias] -> [TableName] -> [[VarName]] -> [B.Table] -> [Function] -> [[VarName]] -> [[Int]] -> [(TableAlias, TableData)]
processAllTables [] [] [] [] [] [] [] = []
processAllTables (tableAlias:xs0) (x1:xs1) (x2:xs2) (x3:xs3) (x4:xs4) (x5:xs5) (x6:xs6) =
    let tableData = processOneTable tableAlias x1 x2 x3 x4 x5 x6 in
    (tableAlias,tableData) : (processAllTables xs0 xs1 xs2 xs3 xs4 xs5 xs6)

processOneTable :: TableAlias -> TableName -> [VarName] -> B.Table -> Function -> [VarName] -> [Int] -> TableData
processOneTable tableAlias tableName inputVars tableValues normFun dbSensitiveVars dbSensitiveRows =

    -- initially, there are no complex functions, only initial variables
    let qFuns = [] in
    let exprs = [] in

    -- let non-sensitive rows be indexed by -1
    let numOfRows             = length tableValues in
    let extendedSensitiveRows = map (\x -> [x]) $ fillMissingWith (-1) numOfRows dbSensitiveRows in

    T tableValues inputVars exprs qFuns [(tableAlias, normFun)] extendedSensitiveRows dbSensitiveVars tableName


deriveExprNorm :: Bool -> Bool -> Int -> (M.Map VarName B.Var) -> S.Set B.Var -> [(TableAlias,Function)] -> B.Expr -> B.TableExpr -> (B.Expr,B.TableExpr,Bool)
deriveExprNorm debug usePrefices numOfSensRows inputMap sensitiveCols allTableNorms queryExpr queryAggr =

    let (dbNormTableAliases, dbNormFuns) = unzip allTableNorms in
    let namePrefices = map (\tableAlias -> if usePrefices then tableAlias ++ "." else "") dbNormTableAliases in
    let (dbNorms1,dbAggrNorms) = unzip $ zipWith (\x y -> norm2Expr x inputMap y) namePrefices dbNormFuns in
    let dbNorms = map (markNormCols sensitiveCols) dbNorms1 in

    -- if there are several tables, we assume that we compute sensitivity w.r.t. max of them
    -- alternatively, we could assign different sensitivity weights to different tables
    let dbExprNorm = NormL Any dbNorms in
    let dbAggrNorm = foldr takeFiner (Exactly 1.0) dbAggrNorms in

    let orderedVars = [0..M.size inputMap - 1] in
    let queryExprNorm = deriveNorm orderedVars queryExpr in
    let queryAggrNorm = deriveTableNorm queryAggr in

    -- adjust the query norm to the table norm
    let newQueryExprNorm = normalizeAndVerify queryExprNorm dbExprNorm in

    --has the adjustment succeeded, or are the norms too different?
    let (goodNorm,(mapCol,mapLN)) = case newQueryExprNorm of
            Just norm -> (True, extractScalings norm)
            Nothing   -> (False, (none,none)) where none = M.empty
    in

    let adjustedQueryExpr = updateExpr mapCol mapLN queryExpr in
    let adjustedQueryAggr = updateTableExpr queryAggr mapCol mapLN queryAggrNorm dbAggrNorm numOfSensRows in

    let newQueryNorm = deriveNorm orderedVars adjustedQueryExpr in
    let newAggrNorm  = deriveTableNorm adjustedQueryAggr in

    traceIfDebug debug ("----------------") $
    traceIfDebug debug (show dbAggrNorms) $
    traceIfDebug debug ("database norm     = Rows: " ++ show dbAggrNorm    ++ " | Cols: "  ++ show (normalizeNorm dbExprNorm)) $
    traceIfDebug debug ("intial query norm = Rows: " ++ show queryAggrNorm ++ " | Cols: "  ++ show (normalizeNorm queryExprNorm)) $
    traceIfDebug debug ("adjust query norm = Rows: " ++ show newAggrNorm   ++ " | Cols: "  ++ show (normalizeNorm newQueryNorm)) $
    traceIfDebug debug ("variable norm scaling: " ++ case newQueryExprNorm of {Nothing -> "???\n"; Just norm -> show (extractScalings norm) ++ "\n"}) $
    traceIfDebug debug ("----------------") $
    (adjustedQueryExpr, adjustedQueryAggr, goodNorm)


filteredExpr :: B.Table -> Double -> (M.Map VarName B.Var) -> [[Int]] -> S.Set B.Var -> [Function] -> [Function] -> ([Function], [[Int]], B.Table)
filteredExpr table infVal inputMap sensRowMatrix sensitiveCols filterFuns unfilteredQueryFuns =

    let numOfRows = length table in

    let (filterVars, filterExprs) = unzip $ map ((\(x,y) -> (S.intersection x sensitiveCols, markExprCols sensitiveCols y)) . query2Expr inputMap) filterFuns in
    let filterValues  = map (\x -> map B.fx $ zipWith B.analyzeExpr table (replicate numOfRows x)) filterExprs in
    let initialFilter = replicate numOfRows True in

    let (filteredQueryFuns,goodRows) = applyFilters initialFilter infVal unfilteredQueryFuns sensRowMatrix filterFuns filterVars filterValues in
    let (filteredTable, filteredSensRowMatrix, _) = unzip3 $ filter (\(x,y,b) -> b) (zip3 table sensRowMatrix goodRows) in
    (filteredQueryFuns, filteredSensRowMatrix, filteredTable)

-- construct input for multitable Banach analyser
-- we read the columns in the order they are given in allTableNorms, since it matches the cross product table itself
inputForSensWrtTable :: Bool -> Bool -> B.Expr -> B.TableExpr -> [(TableAlias,Function)] -> [[Int]] -> (M.Map VarName B.Var) -> (M.Map TableAlias TableData) -> [(Bool, (TableName, [Int], B.TableExpr))]
inputForSensWrtTable debug usePrefices queryExpr queryAggr allTableNorms [] inputMap tableMap =
    error $ error_emptyTable
inputForSensWrtTable debug usePrefices queryExpr queryAggr allTableNorms sensitiveRowMatrix inputMap tableMap =
    let sensitiveRowMatrixColumns = transpose sensitiveRowMatrix in
    let n1 = length sensitiveRowMatrixColumns in
    let n2 = length allTableNorms in
    if n1 /= n2 then error $ error_internal_sensitivityMatrix n1 n2 else
    inputForSensWrtTableRec debug usePrefices inputMap queryExpr queryAggr allTableNorms sensitiveRowMatrixColumns tableMap

inputForSensWrtTableRec :: Bool -> Bool -> (M.Map VarName B.Var) -> B.Expr -> B.TableExpr -> [(TableAlias, Function)] -> [[Int]] -> (M.Map TableAlias TableData) -> [(Bool, (TableName, [Int], B.TableExpr))]
inputForSensWrtTableRec _ _ _ _ _ [] _ _ = []
inputForSensWrtTableRec debug usePrefices inputMap queryExpr queryAggr (tableNorm@(tableAlias, _) : ts) (col:cols) tableMap =

    let tableData     = tableMap ! tableAlias in
    let tableName     = getTableName     tableData in
    let tableSensVars = getSensitiveCols tableData in
    let tableSensCols = S.fromList $ map (inputMap ! ) tableSensVars in

    let newQueryExpr = markExprCols      tableSensCols queryExpr in
    let newQueryAggr = markTableExprCols tableSensCols queryAggr in

    let numOfRows = length col in
    let numOfSensRows = length $ filter (>= 0) col in

    traceIfDebug debug ("num of rows: " ++ show numOfRows) $
    traceIfDebug debug ("num of Sens rows: " ++ show numOfSensRows) $

    let (_,adjustedQueryAggr, goodNorm) = deriveExprNorm debug usePrefices numOfSensRows inputMap tableSensCols [tableNorm] newQueryExpr newQueryAggr in
    (goodNorm, (tableName, col, adjustedQueryAggr)) : inputForSensWrtTableRec debug usePrefices inputMap queryExpr queryAggr ts cols tableMap

-- as in the old solution, this declares a join row sensitive iff at least one of participating rows is sensitive 
-- we use the structure that marks all insensitive entries with '-1'
sensitiveOR :: [[Int]] -> [Bool]
sensitiveOR [] = []
sensitiveOR (row:rows) =
    let rowSet = S.fromList row in
    if S.member (-1) rowSet then False : sensitiveOR rows
    else True : sensitiveOR rows

-- this outputs a trace message only if the flag debug=True is set
traceIfDebug :: Bool -> String -> (a -> a)
traceIfDebug debug msg =
    if debug then trace msg
    else id

traceIOIfDebug :: Bool -> String -> IO ()
traceIOIfDebug debug msg = do
    if debug then traceIO msg
    else return ()

processQuery :: TableAlias -> (M.Map TableName Query) -> TableName -> ([TableAlias],[TableName], [Function], [Function])
processQuery prefix queryMap tableName =

    -- if the table is not in the query map, then it is an input table
    if not (M.member tableName queryMap) then
        ([prefix], [tableName], [], [])
    else
        -- collect all used tables of this query
        let query@(P _ _ groupColnames queryFuns usedAliasMap filters) = queryMap ! tableName in

        -- we do not support 'group by' yet
        if length groupColnames > 0 then error $ error_queryExpr_groupBy else

        -- the subqueries should be of select-type
        let (b, err) = badQFuns queryFuns in
        if prefix /= "" && b then error $ err else

        -- recursively, collect all subqueries and filters used to generate all used tables
        let usedAliases = M.keys usedAliasMap in
        let extPrefix = if prefix == "" then "" else prefix ++ "." in
        let (tableAliases', tableNames', subQFuns', subFilters') = unzip4 $ map (\key -> processQuery (extPrefix ++ key) queryMap (usedAliasMap ! key)) usedAliases in

        let tableAliases = concat tableAliases'    in
        let tableNames   = concat tableNames'      in
        let subQFuns     = concat subQFuns'   in
        let subFilters   = concat subFilters' in

        -- put all query funs and all filters together with the current query's funs and filters
        let curTableName = if prefix == "" then "" else tableName ++ "." in
        let newQueryFuns = map (\(F as b) -> F (updateVariableNames curTableName as ("","")) (updatePreficesTableExpr curTableName ("","") b)) queryFuns in
        let newFilters   = map (\(F as b) -> F (updateVariableNames curTableName as ("","")) (updatePreficesTableExpr curTableName ("","") b)) filters in
        let newSubFilters   = map (\(F as b) -> F (updateVariableNames curTableName as ("","")) (updatePreficesTableExpr curTableName ("","") b)) subFilters in

        let outputQueryFuns = mergeQueryFuns extPrefix newQueryFuns (M.toList usedAliasMap) subQFuns in
        let outputFilters   = newSubFilters ++ mergeQueryFuns extPrefix newFilters (M.toList usedAliasMap) subQFuns in

        trace ("|| " ++ show outputQueryFuns) $
        (tableAliases, tableNames, outputQueryFuns, outputFilters)


-- putting everything together
--getBanachAnalyserInput :: String -> IO (B.Table, B.TableExpr)
getBanachAnalyserInput :: Bool -> String -> IO (B.Table, [(String, [Int], B.TableExpr)])
getBanachAnalyserInput debug input = do

    -- "sqlQuery" parses a single query of the form SELECT ... FROM ... WHERE
    queries <- parseSqlQueryFromFile input
    let usePrefices = True

    -- "query" parses the old format where the query function is computed line by line
    --singleQuery <- parseQueryFromFile input
    --let queries = [singleQuery]
    --let usePrefices = False

    -- extract the tables that should be read from input files
    -- substitute intermediate queries into the aggregated query
    let lastQuery = last queries
    let lastQueryName = getQueryName $ lastQuery
    let queryMap = M.fromList $ map (\query -> (getQueryName query, query)) queries 
    let (inputTableAliases,inputTableNames,outputQueryFuns, outputFilterFuns) = processQuery "" queryMap lastQueryName

    inputTableMap <- readAllTables usePrefices inputTableNames inputTableAliases

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ show inputTableNames
    traceIOIfDebug debug $ show inputTableAliases

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "TableQ " ++ show outputQueryFuns
    traceIOIfDebug debug $ "TableF " ++ show outputFilterFuns

    -- we assume that each input table is used only once, so we take the table cross product as an input
    let (crossProductTable, inputVarList, allTableNorms, sensitiveRowMatrix, sensitiveVarList) = getTableCrossProductData inputTableAliases inputTableMap

    let inputMap        = M.fromList $ zip inputVarList [0..length inputVarList - 1]
    let sensitiveColSet = S.fromList $ map (inputMap ! ) sensitiveVarList

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "All input variables:    " ++ show (M.toList inputMap)
    traceIOIfDebug debug $ "All sensitive cols:     " ++ show sensitiveColSet

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "List of tables: " ++ show (M.keys inputTableMap)
    traceIOIfDebug debug $ "Num of rows before filtering:   " ++ show (length crossProductTable)
    --traceIOIfDebug debug $ "Sensitive row matrix: " ++ show sensitiveRowMatrix

    -- we assume that the final table has one column (in theory, there can be more)
    when (length outputQueryFuns > 1) $ error $ error_queryExpr_singleColumn
    let outputQueryExprs = map (\x -> markExprCols sensitiveColSet $ snd (query2Expr inputMap x)) outputQueryFuns

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Query funs (w/o filter) = " ++ show outputQueryFuns
    traceIOIfDebug debug $ "Query expr (w/o filter) = " ++ show outputQueryExprs

    -- TODO this is CHEATING! thoretically, the best value for 'infinity' is the maximum absolute value amongst those that we aggregate
    -- however, this is a bad idea since it depends on private data and has some sensitivity by itself; we want it to be a constant
    -- let infVal = 10000.0 -- this is more honest, but it gives very bad sensitivities
    let infVal = B.fx $ B.analyzeTableExprOld crossProductTable (B.SelectMax (map (\expr -> B.ComposeL 1.0 [expr]) outputQueryExprs))

    -- we may now apply the filter
    let (filteredQueryFuns, filteredSensRowMatrix, filteredTable) = filteredExpr crossProductTable infVal inputMap sensitiveRowMatrix sensitiveColSet outputFilterFuns outputQueryFuns

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Num of rows after filtering:   " ++ show (length filteredTable)
    traceIOIfDebug debug $ "Filtered sensitive row matrix: " ++ show filteredSensRowMatrix

    -- now transform the main query to a banach expression
    let mainQueryFun = last filteredQueryFuns
    let mainQueryExpr = markExprCols sensitiveColSet $ snd $ query2Expr inputMap mainQueryFun
    let mainQueryAggr = queryExprAggregate mainQueryFun mainQueryExpr

    traceIOIfDebug debug ("----------------")
    traceIOIfDebug debug ("Query funs (w/ filter) = " ++ show (last filteredQueryFuns))
    traceIOIfDebug debug ("Query expr (w/ filter) = " ++ show mainQueryExpr)
    traceIOIfDebug debug ("Query aggr (w/ filter) = " ++ show mainQueryAggr)
    
    --bring the input to the form [(String, [Int], TableExpr)]
    let (goodNorms, tableExprData) = unzip $ inputForSensWrtTable debug usePrefices mainQueryExpr mainQueryAggr allTableNorms filteredSensRowMatrix inputMap inputTableMap

    traceIOIfDebug debug ( "----------------")
    traceIOIfDebug debug ( "good table norms:" ++ show goodNorms)
    traceIOIfDebug debug ( "tableExprData:" ++ show tableExprData)
    traceIOIfDebug debug ( "----------------")

    let possibleErrMsg = concat $ zipWith (\b (tableName,_,_) -> if b then "" else warning_verifyNorm ++ tableName ++ "\n") goodNorms tableExprData
    when (debug || not (null possibleErrMsg)) $ putStrLn $ possibleErrMsg

    return (filteredTable, tableExprData)

    -- Below is the old solution that does not consider sensitivities w.r.t. each table

    -- let numOfRows = length filteredTable
    -- let (adjustedQueryExpr, adjustedQueryAggr, goodNorm) = deriveExprNorm debug usePrefices numOfRows inputMap sensitiveColSet allTableNorms mainQueryExpr mainQueryAggr

    -- let goodNormMsg = "OK: the database norm is at least as large as the query norm."
    -- let badNormMsg  = "WARNING: could not prove that the database norm is at least as large as the query norm."
    -- traceIOIfDebug debug $ if goodNorm then goodNormMsg else badNormMsg

    -- traceIOIfDebug debug $ "----------------"
    -- traceIOIfDebug debug $ "filtered table = " ++ show filteredTable ++ "\n"
    -- traceIOIfDebug debug $ "initial expr = " ++ show mainQueryAggr ++ "\n"
    -- traceIOIfDebug debug $ "adjusted expr = " ++ show adjustedQueryAggr
    -- traceIOIfDebug debug $ "----------------"

    -- let sensitiveRowsCV = sensitiveOR filteredSensRowMatrix
    -- let adjustedQueryAggrWithSensRows = queryExprAggregateSensRows numOfRows sensitiveRowsCV mainQueryFun adjustedQueryExpr
    -- return (filteredTable, adjustedQueryAggrWithSensRows)


