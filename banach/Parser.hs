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
allKeyWordList :: [String]
allKeyWordList = ["output","return",
               "const","^","LN","exp","sqrt","root","scaleNorm","zeroSens","lp","linf","prod","inv","div","min","max","sigmoid","tauoid",
               "selectMin","selectMax","selectProd","selectL"]

allKeyWords :: S.Set String -- set of reserved "words"
allKeyWords = S.fromList allKeyWordList

allCaseInsensKeyWords :: S.Set String -- set of reserved "words"
allCaseInsensKeyWords = S.fromList ["select","as","from","where","not","and","min","max","sum","product","count","distinct","group","by","between"]

-- we agree that this key will be used for the output query
outputTableName :: String
outputTableName = head allKeyWordList

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

filterVarConst :: Bool -> Parser [Function]
filterVarConst pos = do
  aexpr <- aExpr
  op <- order
  c <- signedFloat
  let y = "filt~"
  let as = aexprToExpr y (aexprNormalize $ aexpr)
  let b  = if pos then Filt op y c else FiltNeg op y c
  return [F as b]

filterVarVar :: Bool -> Parser [Function]
filterVarVar pos = do
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
  let b  = if pos then Filt op y 0.0 else FiltNeg op y 0.0
  return [F as b]

-- this filter makes sense only of applied to booleans
-- otherwise, it treats all values that do not equal 0 as 1
filterNocomp :: Bool -> Parser [Function]
filterNocomp pos = do
  aexpr <- aExpr
  let y  = "filt~"
  let as = aexprToExpr y (aexprNormalize $ aexpr)
  let b  = if pos then FiltNeg EQ y 0.0 else Filt EQ y 0.0
  return [F as b]

filterBetween :: Bool -> Parser [Function]
filterBetween pos = do
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

  let bLB  = if pos then Filt GT y 0.0 else FiltNeg GT y 0.0
  let bUB  = if pos then Filt LT y 0.0 else FiltNeg LT y 0.0
  return [F asLB bLB, F asUB bUB]

-- ======================================================================= --
-----------------------------------------------------------------------------
----      The code below does not need to be updated with Banach.hs      ----
-----------------------------------------------------------------------------
sqlFilter :: Parser [Function]
sqlFilter = try sqlFilterNeg <|> sqlFilterPos

sqlFilterPos :: Parser [Function]
sqlFilterPos = sqlFilterMain True

sqlFilterNeg :: Parser [Function]
sqlFilterNeg = do
    caseInsensKeyWord "not"
    qs <- sqlFilterMain False
    return qs

sqlFilterMain :: Bool -> Parser [Function]
sqlFilterMain pos = try (filterBetween pos) <|> try (filterVarConst pos) <|> try (filterVarVar pos) <|> filterNocomp pos

sqlQueries :: Parser (M.Map TableName Query)
sqlQueries = try sqlManyQueries <|> sqlOneQuery

sqlManyQueries :: Parser (M.Map TableName Query)
sqlManyQueries = do
    qs1 <- many sqlAsgnQuery
    qs2  <- sqlAggrQuery
    return $ M.union (concatMaps qs1) qs2

sqlOneQuery :: Parser (M.Map TableName Query)
sqlOneQuery = do
    qs  <- sqlAggrQuery
    return qs

sqlAsgnQuery :: Parser (M.Map TableName Query)
sqlAsgnQuery = do
  tableName <- tableName
  void (asgn)
  (gs,colNames,groups,aexprs,tableNames,tableAliases,filters,internalQueries) <- sqlQuery
  let fs = zipWith3 (\g x y -> F (aexprToExpr y $ aexprNormalize x) (g y)) gs aexprs colNames
  let tableAliasMap = M.fromList $ zip tableAliases tableNames
  let subquery = P groups fs tableAliasMap filters
  return $ M.insert tableName subquery internalQueries

sqlQuery :: Parser ([VarName -> TableExpr],[VarName],[VarName],[AExpr VarName],[TableName],[TableAlias],[Function],(M.Map TableName Query))
sqlQuery = do
  caseInsensKeyWord "select"
  namedAExprs <- sepBy1 namedAExpr (symbol ",")
  let (names, gs, aexprs) = unzip3 namedAExprs

  caseInsensKeyWord "from"
  internalTableData <- sepBy1 internalTable (symbol ",")
  let (tableNames,tableAliases,internalQueries) = unzip3 internalTableData
  filters <- sqlQueryFilter
  groups  <- sqlQueryGroupBy

  return (gs,names,groups,aexprs,tableNames,tableAliases,filters,concatMaps internalQueries)

sqlAggrQuery :: Parser (M.Map TableName Query)
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
  let subquery = P groups queryFuns tableAliasMap filters
  let tableName = outputTableName
  return $ M.insert tableName subquery (concatMaps internalQueries)

internalTable :: Parser (TableName, TableAlias, (M.Map TableName Query))
internalTable = internalTableQuery <|> try internalTableNameAS <|> internalTableName 

-- give the table name and the alias explicitly
internalTableNameAS = do
    tableName <- identifier
    caseInsensKeyWord "as"
    tableAlias <- identifier
    return (tableName, tableAlias, M.empty)

-- the real name of a nested query equals the alias, and we know that there cannot be multiple copies of it
internalTableQuery = do
    (gs,colNames,groups,aexprs,tableNames,tableAliases,filters,internalQueries) <- parens sqlQuery
    caseInsensKeyWord "as"
    tableAlias <- identifier
    let fs = zipWith3 (\g x y -> F (aexprToExpr y $ aexprNormalize x) (g y)) gs aexprs colNames
    let tableAliasMap = M.fromList $ zip tableAliases tableNames
    let subquery = P groups fs tableAliasMap filters
    let tableName = tableAlias
    return (tableAlias, tableAlias, M.insert tableName subquery internalQueries)

-- if an alias is not specified, then the table name is used directly
internalTableName = do
    tableName <- identifier
    return (tableName, tableName, M.empty)

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
  return $ P [] [f] tableAliasMap []

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
--   "[String]"         is the list of columns by which the result should be grouped
--   "[Function]"       is the list of the queried function itself (SELECT x)
--   "[TableName]"      is the list of input tables that are used in the query (FROM x)
--   "[TableAlias]"     is the list of table names that are used in the query (FROM ... AS x)
--   "[Function]"       is the list of filters used in the query (WHERE x)
data Query
  = P [String] [Function] (M.Map TableAlias TableName) [Function]
  deriving (Show)

getQueryGroupNames (P x _ _ _) = x
getQueryFunctions  (P _ x _ _) = x
getQueryAliasMap   (P _ _ x _) = x
getQueryFilters    (P _ _ _ x) = x

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
                     (M.Map VarName a) ->                      -- input variable map
                     (M.Map VarName Expr) ->                   -- assigmnent variable map
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

concatMaps :: (Ord k) => [M.Map k a] -> M.Map k a
concatMaps xs = foldr M.union M.empty xs

-- add all the queries of entire list qs2 to each query of the list qs1
mergeQueryFuns :: [Function] -> [Function] -> [Function]
mergeQueryFuns [] _ = []
mergeQueryFuns (F as b : qs1) qs2 =
    let as2 = concatMaps $ map (\(F as1 _) -> as1) qs2 in
    (F (M.union as as2) b) : (mergeQueryFuns qs1 qs2)

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
getTableCrossProductData :: [TableAlias] -> M.Map TableAlias TableData -> (B.Table, [[Int]], [VarName], [VarName])
getTableCrossProductData tableAliases tableMap =

    let allInputVars     = map (getColNames .      (tableMap ! ) ) tableAliases in
    let allSensitiveVars = map (getSensitiveCols . (tableMap ! ) ) tableAliases in
    let allTables        = map (getTableValues .   (tableMap ! ) ) tableAliases in
    let allSensitiveRows = map (getSensitiveRows . (tableMap ! ) ) tableAliases in

    -- the input variables are concatenated in the order of tables, since each of them describes a column
    let inputVarList     = concat allInputVars in
    let sensitiveVarList = concat allSensitiveVars in

    -- find the cross product of all used tables
    let crossProductTable = tableJoin allTables in

    -- find the cross product of table row indices to remeber which row has come from which table
    let sensitiveRowCrossProduct = vectorJoin allSensitiveRows in

    (crossProductTable, sensitiveRowCrossProduct, inputVarList, sensitiveVarList)


data TableData =
    -- content columnNames exprs norms aggrNorms sensRows sensCols originalTablename 
    T B.Table [VarName] Function [[Int]] [VarName] TableName
  deriving Show

getTableValues   (T x _ _ _ _ _) = x
getColNames      (T _ x _ _ _ _) = x
getNorm          (T _ _ x _ _ _) = x
getSensitiveRows (T _ _ _ x _ _) = x
getSensitiveCols (T _ _ _ _ x _) = x
getTableName     (T _ _ _ _ _ x) = x

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

    -- let non-sensitive rows be indexed by -1
    let numOfRows             = length tableValues in
    let extendedSensitiveRows = map (\x -> [x]) $ fillMissingWith (-1) numOfRows dbSensitiveRows in

    T tableValues inputVars normFun extendedSensitiveRows dbSensitiveVars tableName


deriveExprNorm :: Bool -> Bool -> Int -> (M.Map VarName B.Var) -> S.Set B.Var -> [TableAlias] -> [Function] -> B.Expr -> B.TableExpr -> (B.Expr,B.TableExpr,Bool)
deriveExprNorm debug usePrefices numOfSensRows inputMap sensitiveCols dbNormTableAliases dbNormFuns queryExpr queryAggr =

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
    let (mapCol,mapLN) = normalizeAndVerify queryExprNorm dbExprNorm in

    let adjustedQueryExpr = updateExpr mapCol mapLN queryExpr in
    let adjustedQueryAggr = updateTableExpr queryAggr mapCol mapLN queryAggrNorm dbAggrNorm numOfSensRows in

    let newQueryNorm = deriveNorm orderedVars adjustedQueryExpr in
    let newAggrNorm  = deriveTableNorm adjustedQueryAggr in

    traceIfDebug debug ("----------------") $
    traceIfDebug debug (show dbAggrNorms) $
    traceIfDebug debug ("database norm     = Rows: " ++ show dbAggrNorm    ++ " | Cols: "  ++ show (normalizeNorm dbExprNorm)) $
    traceIfDebug debug ("intial query norm = Rows: " ++ show queryAggrNorm ++ " | Cols: "  ++ show (normalizeNorm queryExprNorm)) $
    traceIfDebug debug ("adjust query norm = Rows: " ++ show newAggrNorm   ++ " | Cols: "  ++ show (normalizeNorm newQueryNorm)) $
    traceIfDebug debug ("scaling: " ++ show mapCol ++ "\n\t " ++ show mapLN ++ "\n\n") $
    traceIfDebug debug ("----------------") $
    (adjustedQueryExpr, adjustedQueryAggr, True)


filteredExpr :: B.Table -> Double -> (M.Map VarName B.Var) -> [[Int]] -> S.Set B.Var -> [Function] -> [Function] -> ([Function], [[Int]], B.Table)
filteredExpr table infVal inputMap sensRowMatrix sensitiveCols filterFuns queryFuns =

    let numOfRows = length table in

    -- collect sensitive variables used by each filter, compute all values upon which a filter makes its decision about a row
    let (filterSensVars, filterExprs) = unzip $ map ((\(x,y) -> (S.intersection x sensitiveCols, markExprCols sensitiveCols y)) . query2Expr inputMap) filterFuns in
    let filterValues  = map (\x -> map B.fx $ zipWith B.analyzeExpr table (replicate numOfRows x)) filterExprs in

    -- we start from all-True filter, and map bad rows to False
    let initialFilter = replicate numOfRows True in

    let (filteredQueryFuns,goodRows) = applyFilters initialFilter infVal queryFuns sensRowMatrix filterFuns filterSensVars filterValues in
    let (filteredTable, filteredSensRowMatrix, _) = unzip3 $ filter (\(x,y,b) -> b) (zip3 table sensRowMatrix goodRows) in
    (filteredQueryFuns, filteredSensRowMatrix, filteredTable)

-- construct input for multitable Banach analyser
-- we read the columns in the order they are given in allTableNorms, since it matches the cross product table itself
inputForSensWrtTable :: Bool -> Bool -> [TableAlias] -> B.Expr -> B.TableExpr -> [[Int]] -> (M.Map VarName B.Var) -> (M.Map TableAlias TableData) -> [(Bool, (TableName, [Int], B.TableExpr))]
inputForSensWrtTable _ _ _ _ _ [] _ _ = error $ error_emptyTable
inputForSensWrtTable debug usePrefices tableAliases queryExpr queryAggr sensitiveRowMatrix inputMap tableMap =
    let sensitiveRowMatrixColumns = transpose sensitiveRowMatrix in
    let n1 = length sensitiveRowMatrixColumns in
    let n2 = length tableAliases in
    if n1 /= n2 then error $ error_internal_sensitivityMatrix n1 n2 else
    inputForSensWrtTableRec debug usePrefices tableAliases queryExpr queryAggr sensitiveRowMatrixColumns inputMap tableMap

inputForSensWrtTableRec :: Bool -> Bool -> [TableAlias] -> B.Expr -> B.TableExpr -> [[Int]] -> (M.Map VarName B.Var) -> (M.Map TableAlias TableData) -> [(Bool, (TableName, [Int], B.TableExpr))]
inputForSensWrtTableRec _ _ [] _ _ _ _ _ = []
inputForSensWrtTableRec debug usePrefices (tableAlias : ts) queryExpr queryAggr (col:cols) inputMap tableMap =

    let tableData     = tableMap ! tableAlias in

    let tableNorm     = getNorm          tableData in
    let tableName     = getTableName     tableData in
    let tableSensVars = getSensitiveCols tableData in
    let tableSensCols = S.fromList $ map (inputMap ! ) tableSensVars in

    let newQueryExpr = markExprCols      tableSensCols queryExpr in
    let newQueryAggr = markTableExprCols tableSensCols queryAggr in

    let numOfRows = length col in
    let numOfSensRows = length $ filter (>= 0) col in

    traceIfDebug debug ("num of rows: " ++ show numOfRows) $
    traceIfDebug debug ("num of Sens rows: " ++ show numOfSensRows) $

    let (_,adjustedQueryAggr, goodNorm) = deriveExprNorm debug usePrefices numOfSensRows inputMap tableSensCols [tableAlias] [tableNorm] newQueryExpr newQueryAggr in
    (goodNorm, (tableName, col, adjustedQueryAggr)) : inputForSensWrtTableRec debug usePrefices ts queryExpr queryAggr cols inputMap tableMap

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

updateVariableNames :: TableAlias -> Function -> Function
updateVariableNames prefix (F as b) =
    let as' = M.map (updatePreficesExpr prefix) $ M.mapKeys (updatePrefices prefix) as in
    let b'  = updatePreficesTableExpr prefix b in
    F as' b'

processQuery :: (M.Map TableName Query) -> TableAlias -> TableName -> ([TableAlias],[TableName], [Function], [Function])
processQuery queryMap tableAlias tableName =

    -- if the table is not in the query map, then it is an input table
    if not (M.member tableName queryMap) then
        ([tableAlias], [tableName], [], [])
    else
        -- collect all used tables of this query
        let query@(P groupColnames queryFuns usedAliasMap filterFuns) = queryMap ! tableName in

        -- we do not support 'group by' yet
        if length groupColnames > 0 then error $ error_queryExpr_groupBy else

        -- the subqueries should be of select-type
        let (iserr, err) = badQFuns queryFuns in
        if tableAlias /= outputTableName && iserr then error $ err else

        -- recursively, collect all subqueries and filters used to generate all used tables
        let usedAliases = M.keys usedAliasMap in
        let (tableAliases', tableNames', subQueryFuns', subFiltFuns') = unzip4 $ map (\key -> processQuery queryMap key (usedAliasMap ! key)) usedAliases in

        let tableAliases  = concat tableAliases' in
        let tableNames    = concat tableNames'   in
        let subQueryFuns  = concat subQueryFuns' in
        let subFiltFuns   = concat subFiltFuns'  in

        -- add the current table alias as a prefix to all variables in all queries and filters
        let extTableAlias = if tableAlias == outputTableName then "" else tableAlias ++ "." in

        let newQueryFuns    = map (updateVariableNames extTableAlias) queryFuns in
        let newFilterFuns   = map (updateVariableNames extTableAlias) filterFuns in

        let newSubQueryFuns = map (updateVariableNames extTableAlias) subQueryFuns in
        let newSubFiltFuns  = map (updateVariableNames extTableAlias) subFiltFuns in

        -- put all subquery funs and all filters together with the current query's funs and filters
        let outputQueryFuns = mergeQueryFuns newQueryFuns newSubQueryFuns in
        let outputFilters   = newSubFiltFuns ++ mergeQueryFuns newFilterFuns newSubQueryFuns in

        (map (extTableAlias ++) tableAliases, tableNames, outputQueryFuns, outputFilters)


-- putting everything together
--getBanachAnalyserInput :: String -> IO (B.Table, B.TableExpr)
getBanachAnalyserInput :: Bool -> String -> IO (B.Table, [(String, [Int], B.TableExpr)])
getBanachAnalyserInput debug input = do

    -- "sqlQuery" parses a single query of the form SELECT ... FROM ... WHERE
    queryMap <- parseSqlQueryFromFile input
    let usePrefices = True

    -- "query" parses the old format where the query function is computed line by line
    --let queryMap = M.fromList [(outputTableName,parseQueryFromFile input)]
    --let usePrefices = False

    -- extract the tables that should be read from input files, take into account copies
    -- substitute intermediate queries into the aggregated query
    let (inputTableAliases, inputTableNames, outputQueryFuns, outputFilterFuns) = processQuery queryMap outputTableName outputTableName

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Input table names:   " ++ show inputTableNames
    traceIOIfDebug debug $ "Input table aliases: " ++ show inputTableAliases

    --traceIOIfDebug debug $ "----------------"
    --traceIOIfDebug debug $ "TableQ " ++ show outputQueryFuns
    --traceIOIfDebug debug $ "TableF " ++ show outputFilterFuns

    -- inputTableMap maps input table aliases to the actual table data that it reads from file (table contents, column names, norm, sensitivities)
    inputTableMap <- readAllTables usePrefices inputTableNames inputTableAliases

    -- we assume that each input table has been copied as many times as it is used, and we take the cross product of all resulting tables
    -- the columns of the cross product are ordered according to the list 'inputTableAliases'
    let (crossProductTable, sensitiveRowMatrix, inputVarList, sensitiveVarList) = getTableCrossProductData inputTableAliases inputTableMap

    -- assign a unique integer to each column name, which is the order of this column in the cross product table
    let inputMap        = M.fromList $ zip inputVarList [0..length inputVarList - 1]
    let sensitiveColSet = S.fromList $ map (inputMap ! ) sensitiveVarList

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "All input variables:    " ++ show (M.toList inputMap)
    traceIOIfDebug debug $ "All sensitive cols:     " ++ show sensitiveColSet
    traceIOIfDebug debug $ "#rows before filtering: " ++ show (length crossProductTable)
    --traceIOIfDebug debug $ "Sensitive row matrix:   " ++ show sensitiveRowMatrix

    -- we assume that the output query table has only one column
    when (length outputQueryFuns > 1) $ error $ error_queryExpr_singleColumn
    let outputQueryFun  = head outputQueryFuns
    let outputQueryExpr = markExprCols sensitiveColSet $ snd $ query2Expr inputMap outputQueryFun

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Query fun  (w/o filter) = " ++ show outputQueryFun
    traceIOIfDebug debug $ "Query expr (w/o filter) = " ++ show outputQueryExpr

    -- TODO this is CHEATING! thoretically, the best value for 'infinity' is the the (max - min) of the values that we aggregate
    -- however, this is a bad idea since it depends on private data and has some sensitivity by itself; we want it to be a constant
    -- let infVal = 10000.0 -- this is more honest, but it gives very bad sensitivities
    let infVal = (B.fx $ B.analyzeTableExprOld crossProductTable $ B.SelectMax [outputQueryExpr]) - 
                 (B.fx $ B.analyzeTableExprOld crossProductTable $ B.SelectMin [outputQueryExpr])

    -- we may now apply the filter
    let (filtQueryFuns, filtSensRowMatrix, filtTable) = filteredExpr crossProductTable infVal inputMap sensitiveRowMatrix sensitiveColSet outputFilterFuns [outputQueryFun]

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "#rows after filtering:  " ++ show (length filtTable)
    --traceIOIfDebug debug $ "Filt. sens. row matrix: " ++ show filtSensRowMatrix

    -- now transform the main query to a banach expression
    let mainQueryFun  = head filtQueryFuns
    let mainQueryExpr = markExprCols sensitiveColSet $ snd $ query2Expr inputMap mainQueryFun
    let mainQueryAggr = queryExprAggregate mainQueryFun mainQueryExpr

    traceIOIfDebug debug ("----------------")
    traceIOIfDebug debug ("Query funs (w/ filter) = " ++ show mainQueryFun)
    traceIOIfDebug debug ("Query expr (w/ filter) = " ++ show mainQueryExpr)
    traceIOIfDebug debug ("Query aggr (w/ filter) = " ++ show mainQueryAggr)
    
    --bring the input to the form [(String, [Int], TableExpr)]
    let (goodNorms, tableExprData) = unzip $ inputForSensWrtTable debug usePrefices inputTableAliases mainQueryExpr mainQueryAggr filtSensRowMatrix inputMap inputTableMap

    traceIOIfDebug debug ( "----------------")
    traceIOIfDebug debug ( "good table norms:" ++ show goodNorms)
    traceIOIfDebug debug ( "tableExprData:" ++ show tableExprData)
    traceIOIfDebug debug ( "----------------")

    let possibleErrMsg = concat $ zipWith (\b (tableName,_,_) -> if b then "" else error_verifyNorm ++ tableName ++ "\n") goodNorms tableExprData
    when (not (null possibleErrMsg)) $ error $ possibleErrMsg

    return (filtTable, tableExprData)


    -- Below is the old solution that does not consider sensitivities w.r.t. each table

    -- let numOfRows = length filtTable
    -- let inputTableNorms = map (getNorm . inputTableMap !) inputTableAliases
    -- let (adjustedQueryExpr, adjustedQueryAggr, goodNorm) = 
    --     deriveExprNorm debug usePrefices numOfRows inputMap sensitiveColSet inputTableAliases inputTableNorms mainQueryExpr mainQueryAggr

    -- let goodNormMsg = "OK: the database norm is at least as large as the query norm."
    -- let badNormMsg  = "WARNING: could not prove that the database norm is at least as large as the query norm."
    -- traceIOIfDebug debug $ if goodNorm then goodNormMsg else badNormMsg

    -- traceIOIfDebug debug $ "----------------"
    -- traceIOIfDebug debug $ "filtered table = " ++ show filtTable ++ "\n"
    -- traceIOIfDebug debug $ "initial expr = " ++ show mainQueryAggr ++ "\n"
    -- traceIOIfDebug debug $ "adjusted expr = " ++ show adjustedQueryAggr
    -- traceIOIfDebug debug $ "----------------"

    -- let sensitiveRowsCV = sensitiveOR filtSensRowMatrix
    -- let adjustedQueryAggrWithSensRows = queryExprAggregateSensRows numOfRows sensitiveRowsCV mainQueryFun adjustedQueryExpr
    -- return (filtTable, adjustedQueryAggrWithSensRows)


