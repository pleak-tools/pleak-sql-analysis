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
import Control.Monad (void)
import Debug.Trace

import Data.Char
import Data.Either
import Data.List
import qualified Data.Map as M
import Data.Map ((!))
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
type TableName = String

-- a small bit, denoting whether we are parsing a query or a norm
-- we define it, since a query and a norm have very similar format
data ParserInstance = QueryParsing | NormParsing

---------------------------------------------------------------------------------------------
-- TODO: parsing of 'expr' and 'tableExpr' is being synchronized with B.Expr and B.TableExpr

-- keywords
allKeyWords :: S.Set String -- set of reserved "words"
allKeyWords = S.fromList ["return",
               "const","^","LN","exp","sqrt","root","scaleNorm","zeroSens","lp","linf","prod","inv","div","min","max","sigmoid",
               "selectMin","selectMax","selectProd","selectL"]

allCaseInsensKeyWords :: S.Set String -- set of reserved "words"
allCaseInsensKeyWords = S.fromList ["select","as","from","where","and","min","max","sum","product","count"]

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

namedAExpr :: Parser (String, AExpr VarName)
namedAExpr = do
    aexpr <- aExpr
    caseInsensKeyWord "as"
    newColName <- identifier
    return (newColName, aexpr)

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

selectAExpr :: Parser (VarName -> TableExpr)
selectAExpr = do
  return Select

filterVarConst :: Parser Function
filterVarConst = do
  aexpr <- aExpr
  op <- order
  c <- signedFloat
  let y = "filt~"
  let as = aexprToExpr y (aexprNormalize $ aexpr)
  let b  = Filt op y c
  return (F as b)

filterVarVar :: Parser Function
filterVarVar = do
  aexpr1 <- aExpr
  op <- order
  aexpr2 <- aExpr
  let y = "filt~"
  let y1 = "filty1~"
  let y2 = "filty2~"
  let z1 = "filtz1~"
  let z2 = "filtz2~"
  let as1 = M.toList $ aexprToExpr y1 (aexprNormalize $ aexpr1)
  let as2 = M.toList $ aexprToExpr y2 (aexprNormalize $ aexpr2)
  let as = M.fromList (as1 ++ as2 ++ [(y, Sum [y1, z2]),(z2, Prod [y2,z1]),(z1, Const (-1.0))])
  let b  = Filt op y 0.0
  return (F as b)

-- ======================================================================= --
-----------------------------------------------------------------------------
----      The code below does not need to be updated with Banach.hs      ----
-----------------------------------------------------------------------------
sqlFilter :: Parser Function
sqlFilter = try filterVarConst <|> filterVarVar

sqlQueries :: Parser [Query]
sqlQueries = try sqlManyQueries <|> sqlOneQuery

sqlManyQueries :: Parser [Query]
sqlManyQueries = do
    qs <- many sqlQuery
    q  <- sqlAggrQuery
    return (qs ++ [q])

sqlOneQuery :: Parser [Query]
sqlOneQuery = do
    q  <- sqlAggrQuery
    return [q]

sqlQuery :: Parser Query
sqlQuery = do
  tableName <- varName
  void (asgn)
  caseInsensKeyWord "select"
  namedAExprs <- sepBy1 namedAExpr (symbol ",")
  let (names,aexprs) = unzip namedAExprs
  caseInsensKeyWord "from"
  tablePaths <- sepBy1 identifier (symbol ",")
  filters    <- sqlQueryFilter
  let fs = zipWith (\x y -> F (aexprToExpr (tableName ++ "." ++ y) $ aexprNormalize x) (Select (tableName ++ "." ++ y))) aexprs names
  return (P tableName names fs tablePaths filters)

sqlAggrQuery :: Parser Query
sqlAggrQuery = do
  caseInsensKeyWord "select"
  g <- sqlAggregator
  aexpr <- aExpr
  let y = "y~"
  caseInsensKeyWord "from"
  tablePaths <- sepBy1 identifier (symbol ",")
  filters    <- sqlQueryFilter
  let as = aexprToExpr y (aexprNormalize $ aexpr)
  let b  = g y
  return (P "output" [] [F as b] tablePaths filters)

sqlQueryFilter :: Parser [Function]
sqlQueryFilter = sqlQueryWithFilter <|> sqlQueryWithoutFilter

sqlQueryWithoutFilter :: Parser [Function]
sqlQueryWithoutFilter = do
  return []

sqlQueryWithFilter :: Parser [Function]
sqlQueryWithFilter = do
  caseInsensKeyWord "where"
  filters <- sepBy1 sqlFilter (caseInsensKeyWord "and")
  return filters

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
  return (P "output" [] [f] [tablePath] [])

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
parseData :: (Parser a) -> String -> String -> a
parseData p err s = 
    let res = parse p "" s in
    case res of
        Left  x -> error (err ++ "\nParse error details:\n" ++ (parseErrorPretty x))
        Right x -> x

parseFromFile :: (Parser a) -> String -> String -> IO a
parseFromFile p err s = fmap (parseData p (err ++ s)) (readInput s)

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
    let table    = readDoubles (Data.List.foldr (\x y -> x ++ "\n" ++ y) "" ls)
    return (varNames, table)

getQueryTableName :: Query -> TableName
getQueryTableName (P tableName _ _ _ _) = tableName

getQueryDbFileNames :: Query -> [String]
getQueryDbFileNames (P _ _ _ dbFileNames _) = dbFileNames

getQueryFilters :: Query -> [Function]
getQueryFilters (P _ _ _ _ filters) = filters

getQueryFunctions :: Query -> [Function]
getQueryFunctions (P _ _ fs _ _) = fs

getQueryColNames :: Query -> [String]
getQueryColNames (P _ cs _ _ _) = cs

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
    let usedInputVarNames = Data.List.filter (\x -> M.member (s ++ x) inputMap) varNames in
    let usedAsgnVarNames  = Data.List.filter (\x -> M.member x asgnMap)  varNames in


    let inputVars        = map (\x -> inputMap ! (s ++ x))                                    usedInputVarNames in
    let asgnInputsExprs  = map (matchAsgnVariable s f inputMap asgnMap) usedAsgnVarNames in

    let (asgnInputs,asgnExprs) = Data.List.unzip asgnInputsExprs in
    (S.union (S.fromList inputVars) (Data.List.foldr S.union S.empty asgnInputs), f expr inputVars asgnExprs asgnInputs)

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

readDoubles :: String -> [[Double]]
readDoubles s = fmap (map read . words) (lines s)

-- add the entire second argument to each query of the first argument list
mergeQueryFuns :: [Function] -> [Function] -> [Function]
mergeQueryFuns [] _ = []
mergeQueryFuns (F as b : qs1) qs2 =
    let as1 = concat $ map (\(F as' _) -> M.toList as') qs2 in
    let as2 = M.fromList as1 in
    (F (M.union as as2) b) : (mergeQueryFuns qs1 qs2)

-- computes full query and filter expressions (as functions), updates the corresponding maps
processQuery :: Query -> (M.Map TableName [Function], M.Map TableName [Function]) -> (M.Map TableName [Function], M.Map TableName [Function])
processQuery (P outputName outputColNames queryFuns inputTableNames filters) (tableQueryMap,tableFilterMap) =
   
    -- find the cross product query of all used input tables
    let inputQFuns      = concat $ map (\x -> tableQueryMap ! x) inputTableNames in
    let inputFilters    = concat $ map (\x -> tableFilterMap ! x) inputTableNames in

    let outputQueryFuns = mergeQueryFuns queryFuns inputQFuns in
    let outputFilters  = inputFilters  ++ mergeQueryFuns filters inputQFuns in

    (M.fromList $ (outputName, outputQueryFuns) : (M.toList tableQueryMap), M.fromList $ (outputName, outputFilters) : (M.toList tableFilterMap))

fillMissingWith :: Int -> Int -> [Int] -> [Int]
fillMissingWith y n xs  = fillMissingWithRec xs y n 0

fillMissingWithRec [] y n i = replicate (n-i) y
fillMissingWithRec (x:xs) y n i =
    if (i == n) then []
    else if (x == i) then x : fillMissingWithRec xs y  n(i+1)
    else if (x > i) then y : fillMissingWithRec (x:xs) y n (i+1)
    else error (error_internal ++ "case x < i in fillMissing: " ++ show x ++ " " ++ show i ++ " " ++ show xs)

-- compute table data for a cross product
getTableCrossProductData :: [TableName] -> M.Map TableName TableData -> TableData
getTableCrossProductData tableNames tableMap =

    let allInputVars       = map (\x -> getColNames (tableMap ! x) ) tableNames in
    let allTables          = map (\x -> getTableValues (tableMap ! x) ) tableNames in
    let allExprs           = map (\x -> getExpr (tableMap ! x) ) tableNames in
    let allQFuns           = map (\x -> getQFun (tableMap ! x) ) tableNames in
    let allNorms         = map (\x -> getNorm (tableMap ! x) ) tableNames in
    let allSensitiveRows = map (\x -> getSensitiveRows (tableMap ! x) ) tableNames in
    let allSensitiveVars = map (\x -> getSensitiveCols (tableMap ! x) ) tableNames in

    -- the expressions are concatenated, since each of them describes a column
    let inputVars   = concat allInputVars in
    let exprs       = concat allExprs in
    let qFuns       = concat allQFuns in
    let norms       = concat allNorms in
    let sensitiveVars = concat allSensitiveVars in

    -- find the cross product of all used tables
    let tableCrossProduct        = tableJoin allTables in

    -- find the cross product of table row indices to remeber which row has come from which table
    let sensitiveRowCrossProduct = vectorJoin allSensitiveRows in

    T tableCrossProduct inputVars exprs qFuns norms sensitiveRowCrossProduct sensitiveVars


data TableData =
    -- content columnNames exprs norms aggrNorms sensRows sensCols
    T B.Table [VarName] [B.Expr] [Function] [(String,Function)] [[Int]] [VarName]
  deriving Show

getTableValues (T x _ _ _ _ _ _) = x 
getColNames    (T _ x _ _ _ _ _) = x 
getExpr        (T _ _ x _ _ _ _) = x 
getQFun        (T _ _ _ x _ _ _) = x 
getNorm        (T _ _ _ _ x _ _) = x
getSensitiveRows (T _ _ _ _ _ x _) = x 
getSensitiveCols (T _ _ _ _ _ _ x) = x 
getNumOfCols   (T _ x _ _ _ _ _) = length x

readAllTables :: Bool -> [TableName] -> IO (M.Map TableName TableData)
readAllTables usePrefices tableNames = do

    -- collect all tables and all column names that will be used in our query
    -- read table sensitivities from corresponding files
    -- mapM is a standard function [IO a] -> IO [a]
    let dbData     = mapM (\tableName -> readDB $ tableName ++ ".db") tableNames
    let dbNormData = mapM (\tableName -> parseNormFromFile $ tableName ++ ".nrm") tableNames

    (tableColNames, tableValues) <- fmap unzip dbData
    (tableSensitives,tableNormFuns)  <- fmap unzip dbNormData
    let (tableSensitiveRows,tableSensitiveVars) = unzip tableSensitives

    -- we put column names inside variables
    let namePrefices = map (\tableName -> if usePrefices then tableName ++ "." else "") tableNames
    let taggedTableColNames = zipWith (\x ys -> map (\y -> x ++ y) ys) namePrefices tableColNames
    let taggedSensitiveVars = zipWith (\x ys -> map (\y -> x ++ y) ys) namePrefices tableSensitiveVars

    -- put all table data together
    let tableMap = processAllTables tableNames taggedTableColNames tableValues tableNormFuns taggedSensitiveVars tableSensitiveRows
    return (M.fromList tableMap)

processAllTables :: [String] -> [[VarName]] -> [B.Table] -> [Function] -> [[VarName]] -> [[Int]] -> [(TableName, TableData)]
processAllTables [] [] [] [] [] [] = []
processAllTables (tableName:xs1) (x2:xs2) (x3:xs3) (x4:xs4) (x5:xs5) (x6:xs6) =
    let tableData = processOneTable tableName x2 x3 x4 x5 x6 in
    (tableName,tableData) : (processAllTables xs1 xs2 xs3 xs4 xs5 xs6)

processOneTable :: String -> [VarName] -> B.Table -> Function -> [VarName] -> [Int] -> TableData
processOneTable tableName inputVars tableValues normFun dbSensitiveVars dbSensitiveRows =

    -- initially, there are no complex functions, only initial variables
    let qFuns = [] in
    let exprs = [] in

    -- let non-sensitive rows be indexed by -1
    let numOfRows             = length tableValues in
    let extendedSensitiveRows = map (\x -> [x]) $ fillMissingWith (-1) numOfRows dbSensitiveRows in

    T tableValues inputVars exprs qFuns [(tableName, normFun)] extendedSensitiveRows dbSensitiveVars


deriveExprNorm :: Bool -> Bool -> Int -> (M.Map VarName B.Var) -> S.Set B.Var -> [(String,Function)] -> B.Expr -> B.TableExpr -> (B.Expr,B.TableExpr,Bool)
deriveExprNorm debug usePrefices numOfRows inputMap sensitiveCols allTableNorms queryExpr queryAggr =

    let (dbNormTableNames, dbNormFuns) = unzip allTableNorms in
    let namePrefices = map (\tableName -> if usePrefices then tableName ++ "." else "") dbNormTableNames in
    let (dbNorms1,dbAggrNorms) = unzip $ zipWith (\x y -> norm2Expr x inputMap y) namePrefices dbNormFuns in
    let dbNorms = map (markNormCols sensitiveCols) dbNorms1 in

    -- if there are several tables, we assume that we compute sensitivity w.r.t. max of them
    -- alternatively, we could assign different sensitivity weights to different tables
    -- TODO check why it does not work correctly with 'Any'
    let dbExprNorm = NormL Any dbNorms in
    let dbAggrNorm = Data.List.foldr takeFiner (Exactly 1.0) dbAggrNorms in

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
    let adjustedQueryAggr = updateTableExpr queryAggr mapCol mapLN queryAggrNorm dbAggrNorm numOfRows in

    let newQueryNorm = deriveNorm [0..M.size inputMap] adjustedQueryExpr in
    let newAggrNorm  = deriveTableNorm adjustedQueryAggr in

    traceIfDebug debug ("----------------") $
    traceIfDebug debug ("database norm     = Rows: " ++ show dbAggrNorm    ++ " | Cols: "  ++ show (normalizeNorm dbExprNorm)) $
    traceIfDebug debug ("intial query norm = Rows: " ++ show queryAggrNorm ++ " | Cols: "  ++ show (normalizeNorm queryExprNorm)) $
    traceIfDebug debug ("adjust query norm = Rows: " ++ show newAggrNorm   ++ " | Cols: "  ++ show (normalizeNorm newQueryNorm)) $
    traceIfDebug debug ("variable norm scaling: " ++ case newQueryExprNorm of {Nothing -> "???\n"; Just norm -> show (extractScalings norm) ++ "\n"}) $
    traceIfDebug debug ("----------------") $
    (adjustedQueryExpr, adjustedQueryAggr, goodNorm)



filteredExpr :: B.Table -> Double -> (M.Map TableName [Function]) -> (M.Map VarName B.Var) -> [[Int]] -> S.Set B.Var -> [Function] -> ([Function], [[Int]], B.Table)
filteredExpr table infVal filterMap inputMap sensRowMatrix sensitiveCols unfilteredQueryFuns =

    let numOfRows = length table in
    let filterFuns = filterMap ! "output" in

    let (filterVars, filterExprs) = unzip $ map ((\(x,y) -> (S.toList $ S.intersection x sensitiveCols, markExprCols sensitiveCols y)) . query2Expr inputMap) filterFuns in
    let filterValues = map (\x -> map B.fx $ zipWith B.analyzeExpr table (replicate numOfRows x)) filterExprs in

    let (filteredQueryFuns, (filteredSensRowMatrix, filteredTable)) = applyFilters infVal unfilteredQueryFuns table sensRowMatrix inputMap filterFuns filterVars filterValues in
    (filteredQueryFuns, filteredSensRowMatrix, filteredTable)


-- construct input for multitable Banach analyser
inputForSensWrtTable :: Bool -> Bool -> B.Expr -> B.TableExpr -> [(String,Function)] -> [[Int]] -> (M.Map VarName B.Var) -> (M.Map String TableData) -> [(Bool, (String, [Int], B.TableExpr))]
inputForSensWrtTable debug usePrefices queryExpr queryAggr allTableNorms [] inputMap tableMap =
    error (error_emptyTable)
inputForSensWrtTable debug usePrefices queryExpr queryAggr allTableNorms sensitiveRowMatrix inputMap tableMap =
    let sensitiveRowMatrixColumns = transpose sensitiveRowMatrix in
    let tableMapList = M.toList tableMap in
    inputForSensWrtTableRec debug usePrefices inputMap queryExpr queryAggr allTableNorms sensitiveRowMatrixColumns tableMapList

inputForSensWrtTableRec :: Bool -> Bool -> (M.Map VarName B.Var) -> B.Expr -> B.TableExpr -> [(String,Function)] -> [[Int]] -> [(String,TableData)] -> [(Bool, (String, [Int], B.TableExpr))]
inputForSensWrtTableRec _ _ _ _ _ _ [] [] = []
inputForSensWrtTableRec debug usePrefices inputMap queryExpr queryAggr allTableNorms (col:cols) ((tableName, tableData) : ts) =
    let tableSensVars = getSensitiveCols tableData in
    let tableSensCols = S.fromList $ map (\x -> inputMap ! x) tableSensVars in
    let newQueryExpr = markExprCols      tableSensCols queryExpr in
    let newQueryAggr = markTableExprCols tableSensCols queryAggr in

    let numOfRows = length col in
    let (_,adjustedQueryAggr, goodNorm) = deriveExprNorm debug usePrefices numOfRows inputMap tableSensCols allTableNorms newQueryExpr newQueryAggr in
    (goodNorm, (tableName, col, adjustedQueryAggr)) : inputForSensWrtTableRec debug usePrefices inputMap queryExpr queryAggr allTableNorms cols ts

inputForSensWrtTableRec _ _ _ _ _ _ _ _ = error (error_internal ++ "table sensitivity matrix and the table map do not match")

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

    -- collect all table names used by all queries, take those that should be read from input files
    let allTableNames    = concat $ map getQueryDbFileNames queries
    let intermTableNames = map getQueryTableName queries
    let inputTableNames  = S.toList $ S.difference (S.fromList allTableNames) (S.fromList intermTableNames)
    inputTableMap <- readAllTables usePrefices inputTableNames

    -- process all queries one by one, get the map that stores final query functions and filters
    let numOfInputTables = length inputTableNames
    let inputQueryMap  = M.fromList $ zip inputTableNames (replicate numOfInputTables [])
    let inputFilterMap = M.fromList $ zip inputTableNames (replicate numOfInputTables [])

    -- queryMap  maps table names to columnwise query expressions
    -- filterMap maps table names to columnwise filter expressions
    let (queryMap, filterMap) = Data.List.foldl (\x y -> processQuery y x) (inputQueryMap,inputFilterMap) queries

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ Data.List.foldr (\(tableName, x) y -> "TableQ " ++ tableName ++ ": " ++ show x ++ "\n\n" ++ y) "" (M.toList queryMap)
    traceIOIfDebug debug $ Data.List.foldr (\(tableName, x) y -> "TableF " ++ tableName ++ ": " ++ show x ++ "\n\n" ++ y) "" (M.toList filterMap)

    -- we assume that each input table is used only once, so we take the table cross product as an input
    let (T crossProductTable allInputVars _ _ allTableNorms sensitiveRowMatrix allSensitiveVars) = getTableCrossProductData inputTableNames inputTableMap
    let inputVarList = zip allInputVars [0..length allInputVars - 1]
    let inputMap = M.fromList inputVarList
    let allSensitiveCols = S.fromList $ map (\x -> inputMap ! x) allSensitiveVars

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "All input variables:    " ++ show (M.toList inputMap)
    traceIOIfDebug debug $ "All sensitive cols:     " ++ show allSensitiveCols

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "List of tables: " ++ show (M.keys inputTableMap)
    traceIOIfDebug debug $ "Sensitive row matrix: " ++ show sensitiveRowMatrix

    -- we assume that the final table has one column (in theory, there can be more)
    let outputQueryFuns  = queryMap ! "output"
    let outputQueryExprs = map (\x -> markExprCols allSensitiveCols $ snd (query2Expr inputMap x)) outputQueryFuns

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Query funs (w/o filter) = " ++ show outputQueryFuns
    traceIOIfDebug debug $ "Query expr (w/o filter) = " ++ show outputQueryExprs

    -- TODO this is CHEATING! thoretically, the best value for 'infinity' is the maximum absolute value amongst those that we aggregate
    -- however, this is a bad idea since it depends on private data and has some sensitivity by itself; we want it to be a constant
    -- let infVal = 10000.0 -- this is more honest, but it gives very bad sensitivities
    let infVal = B.fx $ B.analyzeTableExprOld crossProductTable (B.SelectMax (map (\expr -> B.ComposeL 1.0 [expr]) outputQueryExprs))

    -- we may now apply the filter
    let (filteredQueryFuns, filteredSensRowMatrix, filteredTable) = filteredExpr crossProductTable infVal filterMap inputMap sensitiveRowMatrix allSensitiveCols outputQueryFuns

    traceIOIfDebug debug $ "----------------"
    traceIOIfDebug debug $ "Num of rows after filtering:   " ++ show (length filteredTable)
    traceIOIfDebug debug $ "Filtered sensitive row matrix: " ++ show filteredSensRowMatrix

    -- now transform the main query to a banach expression
    let mainQueryFun = last filteredQueryFuns
    let mainQueryExpr = markExprCols allSensitiveCols $ snd $ query2Expr inputMap mainQueryFun
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
    putStrLn $ possibleErrMsg

    return (filteredTable, tableExprData)

    -- Below is the old solution that does not consider sensitivities w.r.t. each table

    -- let numOfRows = length filteredTable
    -- let (adjustedQueryExpr, adjustedQueryAggr, goodNorm) = deriveExprNorm debug usePrefices numOfRows inputMap allSensitiveCols allTableNorms mainQueryExpr mainQueryAggr

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


