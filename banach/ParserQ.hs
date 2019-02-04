module ParserQ where

import System.Environment
import System.IO.Unsafe

-- some Megaparsec-specific modules
import Text.Megaparsec
import Text.Megaparsec.Expr
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
--
import qualified Control.Exception as Exc
import Control.Monad (void)

import Debug.Trace
import Data.Char
import Data.Either
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Void

import AexprQ
import ErrorMsg
import ExprQ
import NormsQ
import PolicyQ
import QueryQ
import ReaderQ

-- Define the parser type
-- 'Void' means 'no custom error messages'
-- 'String' means 'input comes in form of a String'
type Parser = Parsec Void String


-- we agree that this key will be used for the output query if not specified otherwise
defaultOutputTableName :: String
defaultOutputTableName = "output"

---------------------------------------------------------------------------------------------
-- keywords
allKeyWordList :: [String]
allKeyWordList = ["return","cost","leak",
               "all", "none",
               "const","LN","exp","sqrt","root","scaleNorm","zeroSens","lp","l0","linf","prod","inv","div","min","max","sigmoid","tauoid",
               "selectMin","selectMax","selectProd","selectL"]

allKeyWords :: S.Set String -- set of reserved "words"
allKeyWords = S.fromList allKeyWordList

allCaseInsensKeyWords :: S.Set String -- set of reserved "words"
allCaseInsensKeyWords = S.fromList ["select","as","from","where","not","and","min","max","sum","product","count","distinct","group","by","between","like","in"]

-- a norm expression
normExpr :: Parser [Expr]
normExpr = constExpr
  <|> scaleNormExpr
  <|> scaleNorm2Expr
  <|> zeroSensExpr
  <|> lpNormExpr
  <|> linfNormExpr
  <|> lzeroNormExpr
  <|> lnExpr

-- parsing different expressions, one by one
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

lzeroNormExpr :: Parser [Expr]
lzeroNormExpr = do
  keyWord "l0"
  b <- varName
  return [LZero b]

-- this one is intended only for norms
lnExpr :: Parser [Expr]
lnExpr = do
  keyWord "LN"
  a <- varName
  return [PowerLN a 0.0]

-- a table expression for norms (which norm is applied to the rows)
normTableExpr :: Parser TableExpr
normTableExpr =
  linfTableExpr
  <|> lpTableExpr

-- parsing different expressions, one by one
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

floorAExpr :: Parser (AExpr a -> AExpr a)
floorAExpr = do
  keyWord "floor"
  return (AUnary AFloor)

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

inIntAExpr :: Parser (AExpr VarName -> AExpr VarName)
inIntAExpr = do
  caseInsensKeyWord "in~"
  (a:as) <- parens $ sepBy1 aExpr (symbol ",")
  -- we assume that "in" conditions are mutually exclusive
  return (\e -> foldr (\ae aes -> ABinary AOr (ABinary AEQint e ae) aes) (ABinary AEQint e a) as)

inAExpr :: Parser (AExpr VarName -> AExpr VarName)
inAExpr = do
  caseInsensKeyWord "in"
  (a:as) <- parens $ sepBy1 aExpr (symbol ",")
  -- we assume that "in" conditions are mutually exclusive
  return (\e -> foldr (\ae aes -> ABinary AOr (ABinary AEQ e ae) aes) (ABinary AEQ e a) as)

likeAExpr :: Parser (AExpr VarName -> AExpr VarName)
likeAExpr = do
  caseInsensKeyWord "like"
  aexpr <- aExpr
  return (\e -> ABinary ALike e aexpr)

absBeginAExpr :: Parser (AExpr a -> AExpr a)
absBeginAExpr = do
  symbol "|"
  return (AUnary AAbsBegin)

absEndAExpr :: Parser (AExpr a -> AExpr a)
absEndAExpr = do
  symbol "|"
  return (AUnary AAbsEnd)

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


aExpr :: Parser (AExpr VarName)
aExpr = makeExprParser aTerm aOperators

aOperators :: [[Operator Parser (AExpr VarName)]]
aOperators =
  [ [ Prefix  absBeginAExpr
    , Postfix absEndAExpr]

  , [ Prefix lnAExpr
    , Prefix expAExpr
    , Prefix floorAExpr]

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
  <|> aString
  <|> aDummy

aString = do
  t <- text
  return $ AText ("\'" ++ t ++ "\'")

aDummy = do
  symbol "*"
  return $ AConst 0.0

bExpr :: Parser (AExpr VarName)
bExpr = makeExprParser bTerm bOperators

bOperators :: [[Operator Parser (AExpr VarName)]]
bOperators =
  [
    [ Prefix notAExpr
    , Postfix betweenAExpr
    , Postfix inIntAExpr
    , Postfix inAExpr
    , Postfix likeAExpr]

  , [ InfixL (ABinary ALEint <$ symbol "<=~")
    , InfixL (ABinary ALT <$ symbol "<=")
    , InfixL ((\x y -> AUnary ANot (ABinary AEQint x y)) <$ symbol "<>~")
    , InfixL ((\x y -> AUnary ANot (ABinary AEQ x y)) <$ symbol "<>")
    , InfixL ((\x y -> AUnary ANot (ABinary AEQ x y)) <$ symbol "!=")
    , InfixL (ABinary ALTint <$ symbol "<~")
    , InfixL (ABinary ALT <$ symbol "<")
    , InfixL (ABinary AEQint <$ symbol "=~")
    , InfixL (ABinary AEQ <$ symbol "==")
    , InfixL (ABinary AEQ <$ symbol "=")
    , InfixL (ABinary AGEint <$ symbol ">=~")
    , InfixL (ABinary AGT <$ symbol ">=")
    , InfixL (ABinary AGTint <$ symbol ">~")
    , InfixL (ABinary AGT <$ symbol ">") ]

  , [ InfixL (ABinary AAnd <$ caseInsensKeyWord "and")]
  , [ InfixL (ABinary AOr  <$ caseInsensKeyWord "or")
    , InfixL (ABinary AXor  <$ caseInsensKeyWord "xor")]

  ]

bTerm :: Parser (AExpr VarName)
bTerm = try aExpr <|> parens bExpr

cExpr :: Parser (AExpr (String,VarState))
cExpr = makeExprParser cTerm cOperators

cOperators :: [[Operator Parser (AExpr (String,VarState))]]
cOperators =
  [
    [ InfixL (ABinary AAnd <$ caseInsensKeyWord "and")]
  , [InfixL (ABinary AOr  <$ caseInsensKeyWord "or")]
  ]

cTerm :: Parser (AExpr (String,VarState))
cTerm = try cVarStateStmt <|> parens cExpr

cVarStateStmt :: Parser (AExpr (String,VarState))
cVarStateStmt = do
    a <- varName
    b <- varStateVal
    return $ AVar (a,b)

------------------------------------------------------------
---- Parsing SQL query (simlpified, could be delegated) ----
------------------------------------------------------------
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
  return SelectPlain

-- ======================================================================= --
-----------------------------------------------------------------------------
----      The code below does not need to be updated with Banach.hs      ----
-----------------------------------------------------------------------------
sqlFilterExpr :: Parser [AExpr VarName]
sqlFilterExpr = do
    bexpr <- bExpr
    let aexpr = aexprNormalize bexpr
    -- how many filters we actually have if we split them by "and"?
    let xs = case aexpr of
            AAnds ys -> ys
            _        -> []
    let filters = if length xs == 0 then [aexpr] else xs
    return filters

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
  let fs = zipWith3 (\g x y -> F (aexprFixAbs x) (g y)) gs aexprs colNames
  let tableAliasMap = M.fromList $ zip tableAliases tableNames
  let subquery = P groups fs tableAliasMap filters
  return $ M.insert tableName subquery internalQueries

sqlQuery :: Parser ([VarName -> TableExpr],[VarName],[VarName],[AExpr VarName],[TableName],[TableAlias],[AExpr VarName],(M.Map TableName Query))
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

  let ys = map (\i -> defaultOutputTableName ++ ".c" ++ show i) [0..length gs - 1]
  let queryFuns = zipWith3 (\g aexpr y -> F (aexprFixAbs aexpr) (g y)) gs aexprs ys
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
    let fs = zipWith3 (\g x y -> F (aexprFixAbs x) (g y)) gs aexprs colNames
    let tableAliasMap = M.fromList $ zip tableAliases tableNames
    let subquery = P groups fs tableAliasMap filters
    let tableName = tableAlias
    return (tableAlias, tableAlias, M.insert tableName subquery internalQueries)

-- if an alias is not specified, then the table name is used directly
internalTableName = do
    tableName <- identifier
    return (tableName, tableName, M.empty)

sqlQueryFilter :: Parser [AExpr VarName]
sqlQueryFilter = sqlQueryWithFilter <|> sqlQueryWithoutFilter

sqlQueryWithoutFilter :: Parser [AExpr VarName]
sqlQueryWithoutFilter = do
  return []

sqlQueryWithFilter :: Parser [AExpr VarName]
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

-- we change norm formatting, but we keep the old format as well for compatibility
norm :: M.Map String String -> Parser (([Int], [VarName]), NormFunction, Maybe Double)
norm typeMap = do
    ((rxs, cxs), g) <- newNormHeader <|> oldNormHeader
    f <- customNorm <|> defaultNorm typeMap cxs
    return ((rxs, cxs), f, g)

-- TODO think on default G case for both old and new norms
-- the first row in the norm file is the list of sensitive rows
-- the second row in the norm file is the list of sensitive columns
oldNormHeader :: Parser (([Int], [VarName]), Maybe Double)
oldNormHeader = do
  kw  <- readKeyWord "all" <|> readKeyWord "none" <|> return ""
  is' <- many integer
  let is = if kw == "all" then [0..]
           else if kw == "none" then []
           else is'
  xs <- many varName
  void (delim)
  return ((is, xs), Just (1/0))

newNormHeader :: Parser (([Int], [VarName]), Maybe Double)
newNormHeader = do
  readKeyWord "rows:"
  rkw  <- readKeyWord "all" <|> readKeyWord "none" <|> return ""
  rxs' <- many integer
  void (delim)
  let rxs = if rkw == "all" then [0..]
           else if rkw == "none" then []
           else rxs'
  readKeyWord "cols:"
  ckw  <- readKeyWord "all" <|> readKeyWord "none" <|> return ""
  cxs' <- many varName
  void (delim)
  -- TODO maybe, add also possiblity of "all"
  let cxs = if ckw == "none" then []
            else cxs'
  mg <- (do
           readKeyWord "G:"
           g <- float
           void (delim)
           return (Just g)
        ) <|> return (Just (1/0))
  return ((rxs, cxs), mg)

customNorm = do
  f <- function
  return f

defaultNorm typeMap xs = do
  -- if we succeed in reading the identifier, then something is wrong
  let ys = map (\x -> if typeMap ! x == "text" || typeMap ! x == "bool" then LZero x else Id x) xs
  let zs = map (\i -> defaultNormVariable ++ show i) [0..length ys - 1]
  let as = zip zs ys
  let f = NF (M.fromList $ (defaultNormVariable, L 1.0 zs) : as) (SelectL 1.0 defaultNormVariable)
  return f

asgnStmt :: Parser [(VarName,Expr)]
asgnStmt = do
  a  <- varName
  void (asgn)
  bs <- normExpr

  -- this introduces new temporary variables for complex expressions 
  -- here "~" can be any symbol that is not allowed to use in variable names
  let as = map (\x -> a ++ "~" ++ show x) [1 .. length bs - 1]
  void (delim)
  return (zip (a:as) bs)

returnStmt :: Parser TableExpr
returnStmt = do
  keyWord "return"
  a <- normTableExpr
  void (delim)
  return a

function :: Parser NormFunction
function = do
  ass <- many asgnStmt
  b  <- returnStmt
  let as = concat ass
  return (NF (M.fromList as) b)

------------------------------------------
---- Parsing policy and attacker file ----
------------------------------------------
policy :: Parser [(M.Map String VarState, Double)]
policy = sensitiveFormula <|> many sensitiveSet

sensitiveFormula :: Parser [(M.Map String VarState, Double)]
sensitiveFormula = do

    cexpr <- cExpr
    let cs = (fromDNFtoList . toDNF) cexpr
    let n = length cs

    let stateMapList = map M.fromList cs
    c <- costValue
    let costList = replicate n (c / fromIntegral n)

    return $ zip stateMapList costList

sensitiveSet :: Parser (M.Map String VarState, Double)
sensitiveSet = do
  keyWord "leak"
  ps <- many varStateStmt
  c <- costValue
  return (M.fromList ps, c)

costValue :: Parser Double
costValue = do
  keyWord "cost"
  c <- float
  return c

attacker :: Parser (M.Map String VarState)
attacker = do
  ps <- many varStateStmt
  return (M.fromList ps)

varStateStmt :: Parser (String,VarState)
varStateStmt = do
  a <- varName
  b <- varStateVal
  void (delim)
  return (a,b)

varStateVal :: Parser VarState
varStateVal = varStateExact
  <|> varStateNone
  <|> varStateApprox
  <|> varStateTotalUnif
  <|> varStateTotal
  <|> varStateRangeUnif
  <|> varStateSetUnif
  <|> varStateRangePrior
  <|> varStateSetPrior
  <|> varStateRange
  <|> varStateSet

varStateExact = do
  keyWord "exact"
  return Exact

varStateApprox = do
  keyWord "approx"
  r  <- float
  return (Approx r)

varStateTotal = do
  keyWord "total"
  r  <- integer
  return (Total r)

varStateRange = do
  keyWord "range"
  lb <- signedFloat
  ub <- signedFloat
  return (Range lb ub)

varStateSet = do
  keyWord "set"
  xs <- many quotedString
  let xs1 = lefts xs
  let xs2 = rights xs
  let y = if length xs1 > 0 && length xs2 > 0 then error $ error_badSetPolicyFormat xs1 xs2
          else if length xs1 > 0 then SubSet xs1
          else IntSubSet xs2
  return y

varStateTotalUnif = do
  keyWord "totalUnif"
  r  <- integer
  return (TotalUn r)

varStateRangeUnif = do
  keyWord "rangeUnif"
  lb <- signedFloat
  ub <- signedFloat
  return (RangeUn lb ub)

varStateSetUnif = do
  keyWord "setUnif"
  xs <- many quotedString
  let xs1 = lefts xs
  let xs2 = rights xs
  let y = if length xs1 > 0 && length xs2 > 0 then error $ error_badSetPolicyFormat xs1 xs2
          else if length xs1 > 0 then SubSetUn xs1
          else IntSubSetUn xs2
  return y

varStateRangePrior = do
  keyWord "rangePrior"
  lb <- signedFloat
  xs <- many varStateRangePriorPair
  return $ RangePr lb (M.fromList xs)

varStateRangePriorPair = do
  symbol "("
  x <- signedFloat
  symbol ","
  p <- float
  symbol ")"
  return (x,p)

varStateSetPrior = do
  keyWord "setPrior"
  zs <- many varStateSetPriorPair
  let (xs,ys) = unzip zs
  let xs1 = lefts xs
  let xs2 = rights xs
  let y = if length xs1 > 0 && length xs2 > 0 then error $ error_badSetPolicyFormat xs1 xs2
          else if length xs1 > 0 then SubSetPr $ M.fromList (zip xs1 ys)
          else IntSubSetPr $ M.fromList (zip xs2 ys)
  return y

varStateSetPriorPair = do
  symbol "("
  x <- quotedString
  symbol ","
  p <- float
  symbol ")"
  return (x,p)

varStateNone = do
  keyWord "none"
  return None

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
lineComment = "--"

lineComment2 :: String
lineComment2 = "//"

-- block comment
blockCommentStart :: String
blockCommentStart = "/*"

blockCommentEnd :: String
blockCommentEnd = "*/"

-------------------------------------
---- Some auxiliary subparsers   ----
-------------------------------------

-- a keyword
keyWord :: String -> Parser ()
keyWord w = lexeme (C.string w *> notFollowedBy C.alphaNumChar)

readKeyWord :: String -> Parser String
readKeyWord w = do
    lexeme (C.string w *> notFollowedBy C.alphaNumChar)
    return w

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
text = lexeme (C.char '\'' >> manyTill L.charLiteral (C.char '\''))

-- this thing eats all spaces and comments
spaceConsumer :: Parser ()
spaceConsumer = 
        L.space C.space1 lineCmnt blockCmnt
    where
        lineCmnt  = L.skipLineComment lineComment <|> L.skipLineComment lineComment2
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

--floatAsString :: Parser String
--floatAsString = try text <|> fmap show signedFloat

quotedString :: Parser (Either String Int)
quotedString = fmap (\s -> Left ("\'" ++ s ++ "\'")) text <|> fmap Right integer

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

--------------------------
---- Parser embedding ----
--------------------------

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

parsePolicyFromFile fileName   = if fileName == "" then do return [] else parseFromFile policy error_parsePolicy fileName
parseAttackerFromFile fileName = if fileName == "" then do return M.empty else parseFromFile attacker error_parseAttacker fileName
parseNormFromFile typeMap fileName = parseFromFile (norm typeMap) error_parseNorm fileName
--parseNormsFromFile fileName = do
--    r <- parseFromFile norm error_parseNorm fileName
--    return [r]
parseSqlQueryFromFile fileName = parseFromFile sqlQueries error_parseSqlQuery fileName

