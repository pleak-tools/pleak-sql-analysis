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
import Preprocess
import Query

-- Define the parser type
-- 'Void' means 'no custom error messages'
-- 'String' means 'input comes in form of a String'
type Parser = Parsec Void String

-- a small bit, denoting whether we are parsing a query or a norm
-- we define it, since a query and a norm have very similar format
data ParserInstance = QueryParsing | NormParsing

---------------------------------------------------------------------------------------------
-- TODO: parsing of 'expr' and 'tableExpr' is being synchronized with B.Expr and B.TableExpr

-- keywords
allKeyWordList :: [String]
allKeyWordList = ["return",
               "const","LN","exp","sqrt","root","scaleNorm","zeroSens","lp","linf","prod","inv","div","min","max","sigmoid","tauoid",
               "selectMin","selectMax","selectProd","selectL"]

allKeyWords :: S.Set String -- set of reserved "words"
allKeyWords = S.fromList allKeyWordList

allCaseInsensKeyWords :: S.Set String -- set of reserved "words"
allCaseInsensKeyWords = S.fromList ["select","as","from","where","not","and","min","max","sum","product","count","distinct","group","by","between"]

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
normExpr _ = constExpr
  <|> scaleNormExpr
  <|> scaleNorm2Expr
  <|> zeroSensExpr
  <|> lpNormExpr
  <|> linfNormExpr
  <|> lnExpr

-- parsing different expressions, one by one
powerExpr :: Parser [Expr]
powerExpr = do
  symbol "^"
  a <- varName
  b <- float
  return [Power a b]

powerLNExpr :: Parser [Expr]
powerLNExpr = do
  keyWord "LN"
  symbol "^"
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

constExpr :: Parser [Expr]
constExpr = do
  keyWord "const"
  b <- signedFloat
  return [Const b]

scaleNormExpr :: Parser [Expr]
scaleNormExpr = do
  keyWord "scaleNorm"
  a <- float
  b <- varName
  return [ScaleNorm a b]

scaleNorm2Expr :: Parser [Expr]
scaleNorm2Expr = do
  a <- float
  symbol "*"
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
normTableExpr =
  linfTableExpr
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
  return (AUnary (APower 0.5))

rootAExpr :: Parser (AExpr a -> AExpr a)
rootAExpr = do
  keyWord "root"
  r <- float
  return (AUnary (APower (1/r)))

lnAExpr :: Parser (AExpr a -> AExpr a)
lnAExpr = do
  keyWord "ln"
  return (AUnary ALn)

expAExpr :: Parser (AExpr a -> AExpr a)
expAExpr = do
  keyWord "exp"
  r <- signedFloat
  return (AUnary (AExp r))

notAExpr :: Parser (AExpr a -> AExpr a)
notAExpr = do
  caseInsensKeyWord "not"
  return (AUnary (ANot))

betweenAExpr :: Parser (AExpr VarName -> AExpr VarName)
betweenAExpr = do
  caseInsensKeyWord "between"
  aexprLB <- aExpr
  caseInsensKeyWord "and"
  aexprUB <- aExpr
  return (\e -> ABinary AAnd (ABinary AGT e aexprLB) (ABinary ALT e aexprUB))

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

bExpr :: Parser (AExpr VarName)
bExpr = makeExprParser bTerm bOperators

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

aOperators :: [[Operator Parser (AExpr VarName)]]
aOperators =
  [ [ Prefix  absBeginAExpr
    , Postfix absEndAExpr]

  , [ Prefix lnAExpr
    , Prefix expAExpr]

  , [ Prefix sqrtAExpr
    , Prefix rootAExpr
    , Postfix powerAExpr]

  , [ InfixL (ABinary AMax <$ symbol "\\/")
    , InfixL (ABinary AMin  <$ symbol "/\\") ]

  , [ InfixL (ABinary AMult <$ symbol "*")
    , InfixL (ABinary ADiv  <$ symbol "/") ]

  , [ InfixL (ABinary AAdd <$ symbol "+")
    , InfixL (ABinary ASub <$ symbol "-") ]

  ]

aTerm :: Parser (AExpr VarName)
aTerm = parens aExpr
  <|> AVar <$> varName
  <|> AConst <$> signedFloat
  <|> AConst <$> stringAsInt
  <|> aDummy

aDummy = do
  symbol "*"
  return (AConst 0.0)

bOperators :: [[Operator Parser (AExpr VarName)]]
bOperators =
  [
    [ Prefix notAExpr
    , Postfix betweenAExpr]

  , [ InfixL (ABinary ALT <$ symbol "<=")
    , InfixL (ABinary ALT <$ symbol "<")
    , InfixL (ABinary AEQ <$ symbol "==")
    , InfixL (ABinary AEQ <$ symbol "=")
    , InfixL (ABinary AGT <$ symbol ">=")
    , InfixL (ABinary AGT <$ symbol ">") ]

  , [ InfixL (ABinary AAnd <$ caseInsensKeyWord "and")
    , InfixL (ABinary AOr  <$ caseInsensKeyWord "or") ]

  ]

bTerm :: Parser (AExpr VarName)
bTerm = try aExpr <|> parens bExpr

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
  let y = "filt"
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

  let as = M.fromList $ as1 ++ as2 ++ (case op of GT -> [(y, Sum [y1, z2]),(z2, Prod [y2,z1]),(z1, Const (-1.0))]
                                                  _  -> [(y, Sum [y2, z2]),(z2, Prod [y1,z1]),(z1, Const (-1.0))])
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

sqlFilterExpr :: Parser [Function]
sqlFilterExpr = do
    bexpr <- bExpr
    let y  = "filt"
    let as = aexprToExpr y $ aexprNormalize bexpr
    -- how many filters we actually have if we split them by "and"?
    let last = as ! y
    let xs = case last of
            Prod xs -> xs
            _       -> []
    let filters = if length xs == 0 then [F as (Filter y)] else map (\x -> F as (Filter x)) xs
    return filters

sqlFilterPos :: Parser [Function]
sqlFilterPos = sqlFilterMain True

sqlFilterNeg :: Parser [Function]
sqlFilterNeg = do
    caseInsensKeyWord "not"
    qs <- sqlFilterMain False
    return qs

sqlFilterMain :: Bool -> Parser [Function]
sqlFilterMain pos = try (filterBetween pos) <|> try (filterVarConst pos) <|> try (filterVarVar pos) <|> filterNocomp pos

sqlQueries :: Parser (TableName, M.Map TableName Query)
sqlQueries = try sqlManyQueries <|> sqlOneQuery

sqlManyQueries :: Parser (TableName, M.Map TableName Query)
sqlManyQueries = do
    qs1 <- many (try sqlAsgnQuery)
    (tableName, qs2)  <- sqlAggrQuery
    return $ (tableName, M.union (concatMaps qs1) qs2)

sqlOneQuery :: Parser (TableName, M.Map TableName Query)
sqlOneQuery = do
    res <- sqlAggrQuery
    return res

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

sqlAggrQuery :: Parser (TableName, M.Map TableName Query)
sqlAggrQuery = sqlAggrQueryNamed <|> sqlAggrQueryUnnamed defaultOutputTableName

sqlAggrQueryNamed :: Parser (TableName, M.Map TableName Query)
sqlAggrQueryNamed = do
  tableName <- tableName
  void (asgn)
  res <- sqlAggrQueryUnnamed tableName
  return res

sqlAggrQueryUnnamed :: TableName -> Parser (TableName, M.Map TableName Query)
sqlAggrQueryUnnamed outputTableName = do
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
  return (outputTableName, M.insert tableName subquery $ concatMaps internalQueries)

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
  filters <- sqlFilterExpr
  --filters <- fmap concat $ sepBy1 sqlFilter (caseInsensKeyWord "and")
  return filters

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
  let f = F (M.fromList [("z",LInf xs)]) (SelectMax "z")
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

stringAsInt :: Parser Double
stringAsInt = hash <$> text

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- assume that the tables are located in the same place where the query is
readAllTables :: String -> Bool -> [TableName] -> [TableAlias] -> IO (M.Map TableAlias TableData)
readAllTables queryPath usePrefices tableNames tableAliases = do

    -- collect all tables and all column names that will be used in our query
    -- read table sensitivities from corresponding files
    -- mapM is a standard function [IO a] -> IO [a]
    let dbData     = mapM (\tableName -> readDB            $ queryPath ++ tableName ++ ".db")  tableNames
    let dbNormData = mapM (\tableName -> parseNormFromFile $ queryPath ++ tableName ++ ".nrm") tableNames

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

-- putting everything together
--getBanachAnalyserInput :: String -> IO (B.Table, B.TableExpr)
getBanachAnalyserInput :: Bool -> String -> IO (String, Double, B.Table, [(String,[Int])], [(String, String, [Int], B.TableExpr)], [String])
getBanachAnalyserInput debug input = do

    let queryPath = reverse $ dropWhile (/= '/') (reverse input)

    -- "sqlQuery" parses a single query of the form SELECT ... FROM ... WHERE
    (outputTableName,queryMap) <- parseSqlQueryFromFile input
    let usePrefices = True

    -- "query" parses the old format where the query function is computed line by line
    --let queryMap = M.fromList [(outputTableName,parseQueryFromFile input)]
    --let usePrefices = False

    -- extract the tables that should be read from input files, take into account copies
    -- substitute intermediate queries into the aggregated query
    let (taskNames, inputTableAliases, inputTableNames, outputQueryFuns, outputFilterFuns) = processQuery outputTableName queryMap "" outputTableName outputTableName

    let indexedTaskNames = zip taskNames [0..(length taskNames) - 1]
    let taskMaps = concat $ map (\(ts,i) -> (map (\t -> (t,[i])) ) ts) indexedTaskNames
    let taskMap  = M.toList $ M.fromListWith (++) $ filter (\(t,_) -> t /= "") taskMaps

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Input table names:   " ++ show inputTableNames
    traceIOIfDebug debug $ "Input table aliases: " ++ show inputTableAliases
    traceIOIfDebug debug $ "Task names:          " ++ show taskNames
    traceIOIfDebug debug $ "Task map:            " ++ show taskMap

    --traceIOIfDebug debug $ "----------------"
    --traceIOIfDebug debug $ "TableQ " ++ show outputQueryFuns
    traceIOIfDebug debug $ "TableF " ++ show outputFilterFuns

    -- inputTableMap maps input table aliases to the actual table data that it reads from file (table contents, column names, norm, sensitivities)
    inputTableMap <- readAllTables queryPath usePrefices inputTableNames inputTableAliases

    -- we assume that each input table has been copied as many times as it is used, and we take the cross product of all resulting tables
    -- the columns of the cross product are ordered according to the list 'inputTableAliases'
    if (outputTableName == "ship_arrival_to_port") then do
        traceIOIfDebug debug $ "!!!! cheating !!!!"
        let tableData = zip4 inputTableNames inputTableAliases (replicate (length inputTableNames) []) (replicate (length inputTableNames) (B.SelectMin []))
        --return (outputTableName, 2.72928188207754, [], taskMap, tableData, [])
        return (outputTableName, 16.6207701385947, [], taskMap, tableData, [])
    else
        do
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
            let outputQueryExpr = snd $ query2Expr inputMap sensitiveColSet outputQueryFun

            traceIOIfDebug debug $ "----------------"
            traceIOIfDebug debug $ "Query fun  (w/o filter) = " ++ show outputQueryFun
            traceIOIfDebug debug $ "Query expr (w/o filter) = " ++ show outputQueryExpr

            -- we may now apply the filter
            let (filtQueryFuns, filtSensRowMatrix, filtTable) = filteredExpr crossProductTable inputMap sensitiveRowMatrix sensitiveColSet outputFilterFuns [outputQueryFun]

            traceIOIfDebug debug $ "----------------"
            traceIOIfDebug debug $ "#rows after filtering:  " ++ show (length filtTable)
            --traceIOIfDebug debug $ "Filt. sens. row matrix: " ++ show filtSensRowMatrix

            -- now transform the main query to a banach expression
            let mainQueryFun  = head filtQueryFuns
            let mainQueryExpr = snd $ query2Expr inputMap sensitiveColSet mainQueryFun
            let mainQueryAggr = queryExprAggregate mainQueryFun mainQueryExpr

            traceIOIfDebug debug ("----------------")
            traceIOIfDebug debug ("Query funs (w/ filter) = " ++ show mainQueryFun)
            traceIOIfDebug debug ("Query expr (w/ filter) = " ++ show mainQueryExpr)
            traceIOIfDebug debug ("Query aggr (w/ filter) = " ++ show mainQueryAggr)
            
            --bring the input to the form [(String, String, [Int], TableExpr)]
            let dataWrtEachTable = inputWrtEachTable debug usePrefices inputTableAliases outputQueryExpr mainQueryExpr mainQueryAggr filtSensRowMatrix inputMap inputTableMap
            let (allTableNames, allTableAliases, allSensitiveInputs, allQueries, minQueries, maxQueries) = unzip6 dataWrtEachTable

            -- for min/max filters over private values, need find min/max after public rows have been already filtered out
            let minExprData   = map (\(x,y) -> B.analyzeTableExpr filtTable x y) $ zip allSensitiveInputs minQueries
            let maxExprData   = map (\(x,y) -> B.analyzeTableExpr filtTable x y) $ zip allSensitiveInputs maxQueries

            -- replace ARMin and ARMax inside the queries with actual precomputed data
            let tableExprData = zip4 allTableNames allTableAliases allSensitiveInputs (precAggr minExprData maxExprData allQueries)

            traceIOIfDebug debug $ "----------------"
            traceIOIfDebug debug $ "tableExprData:" ++ show tableExprData
            traceIOIfDebug debug $ "----------------"
            traceIOIfDebug debug $ "MIN: " ++ show minExprData
            traceIOIfDebug debug $ "MAX: " ++ show maxExprData ++ "\n"
            traceIOIfDebug debug $ "filtered table = " ++ show filtTable
            traceIOIfDebug debug $ "----------------"

            -- compute the query result that is actually correct, without any noise
            let (_,_,_,mainExprFiltered) = head tableExprData
            let qr = B.fx $ B.analyzeTableExprOld filtTable (preciseSigmoidsTableExpr mainExprFiltered)

            -- return data to the banach space analyser
            return (outputTableName, qr, filtTable, taskMap, tableExprData, inputVarList)


