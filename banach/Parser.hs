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
import Data.Either
import Data.List
import Data.Map
import qualified Data.Set as S
import Data.Void

-- import Expr directly from Banach.hs, 'qualified' because we want to reuse the names
import qualified Banach as B
import Aexpr
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
allKeyWords :: [String] -- list of reserved "words"
allKeyWords = ["return",
               "const","^","LN","exp","sqrt","root","scaleNorm","zeroSens","lp","linf","prod","inv","div","min","max","sigmoid",
               "selectMin","selectMax","selectProd","selectL",
               "SELECT","AS","FROM","WHERE","AND"]

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
    keyWord "AS"
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


------------------------------------------------------------
---- Parsing SQL query (simlpified, could be delegated) ----
------------------------------------------------------------
order :: Parser Ordering
order = ordLT <|> ordEQ <|> ordGT
ordLT = do
  symbol "<="
  return LT
ordEQ = do
  symbol "=="
  return EQ
ordGT = do
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
  keyWord "PRODUCT"
  return SelectProd

selectMinAExpr :: Parser (VarName -> TableExpr)
selectMinAExpr = do
  keyWord "MIN"
  return SelectMin

selectMaxAExpr :: Parser (VarName -> TableExpr)
selectMaxAExpr = do
  keyWord "MAX"
  return SelectMax

selectSumAExpr :: Parser (VarName -> TableExpr)
selectSumAExpr = do
  keyWord "SUM"
  return SelectSum

selectCountAExpr :: Parser (VarName -> TableExpr)
selectCountAExpr = do
  keyWord "COUNT"
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
  let as1 = toList $ aexprToExpr y1 (aexprNormalize $ aexpr1)
  let as2 = toList $ aexprToExpr y2 (aexprNormalize $ aexpr2)
  let as = fromList (as1 ++ as2 ++ [(y, Sum [y1, z2]),(z2, Prod [y2,z1]),(z1, Const (-1.0))])
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
  keyWord "SELECT"
  namedAExprs <- sepBy1 namedAExpr (symbol ",")
  let (names,aexprs) = unzip namedAExprs
  keyWord "FROM"
  tablePaths <- sepBy1 identifier (symbol ",")
  filters    <- sqlQueryFilter
  let fs = zipWith (\x y -> F (aexprToExpr (tableName ++ "." ++ y) $ aexprNormalize x) (Select (tableName ++ "." ++ y))) aexprs names
  return (P tableName names fs tablePaths filters)

sqlAggrQuery :: Parser Query
sqlAggrQuery = do
  keyWord "SELECT"
  g <- sqlAggregator
  aexpr <- aExpr
  let y = "y~"
  keyWord "FROM"
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
  keyWord "WHERE"
  filters <- sepBy1 sqlFilter (keyWord "AND")
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
  let f = F (fromList [("z",L 1.0 xs)]) (SelectMax "z")
  return f

asgnStmt :: ParserInstance -> Parser [(VarName,Expr)]
asgnStmt p = do
  a  <- varName
  void (asgn)
  bs <- case p of {QueryParsing -> queryExpr a; NormParsing -> normExpr a}
  -- this introduces new temporary variables for complex expressions 
  -- here "~" can be any symbol that is not allowed to use in variable names
  let as = Data.List.map (\x -> a ++ "~" ++ show x) [1 .. length bs - 1]
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
  return (F (fromList as) b)


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
parseData :: (Parser a) -> String -> a
parseData p s = 
    let res = parse p "" s in
    case res of
        Left  x -> error ("Parse error:\n" ++ (parseErrorPretty x))
        Right x -> x

parseFromFile :: (Parser a) -> String -> IO a
parseFromFile p s = fmap (parseData p) (readInput s)

parseTestFromFile :: (Show a, ShowErrorComponent e) => Parsec e String a -> FilePath -> IO ()
parseTestFromFile p s = parseTest p (unsafePerformIO (readInput s))

-- a keyword
keyWord :: String -> Parser ()
keyWord w = lexeme (C.string w *> notFollowedBy C.alphaNumChar)

-- variable identifier, as taken from the tutorial
-- it checks that the identifier is not a keyword
identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p       = (:) <$> C.letterChar <*> many alphaNumCharAndPeriod
    check x = if elem x allKeyWords
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
float = lexeme L.float

-- reads a signed double
signedFloat :: Parser Double
signedFloat = L.signed spaceConsumer float

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

query2Expr :: [VarName] -> (Map VarName B.Var) -> Function -> ([B.Var], B.Expr)
query2Expr sensitiveVars inputMap (F asgnMap y) =
    let x = extractArg y in
    let sensitiveCols = S.fromList (Data.List.map (\x -> inputMap ! x) sensitiveVars) in
    let (usedVars,z) = matchAsgnVariable "" queryExpression B.ZeroSens sensitiveCols inputMap asgnMap x in
    (S.toList usedVars, z)

queryExprAggregate :: Int -> [Bool] -> Function-> B.Expr -> B.TableExpr
queryExprAggregate numOfRows sensitiveRowsCV  (F _ y) z = 
    let zs = zipWith (\x y -> if x then y else B.ZeroSens y) sensitiveRowsCV (replicate numOfRows z) in
    queryArg y zs

norm2Expr :: (Show a, Ord a) => String -> [VarName] -> (Map VarName a) -> Function -> (Norm a, ADouble)
norm2Expr prefix sensitiveVars inputMap (F asgnMap y) =
    let x = extractArg y in
    let sensitiveCols = S.fromList (Data.List.map (\x -> inputMap ! x) sensitiveVars) in
    let (_,z) = matchAsgnVariable prefix normExpression NormZero sensitiveCols inputMap asgnMap x in
    (z, normArg y)

processExpression :: (Show a, Ord a) => 
                     String ->                                 -- the name of the database file that we prepend to all variable names
                     (Expr -> [a] -> [b] -> [S.Set a] -> b) -> -- the function that actually rewrites the term
                     (b -> b) ->                               -- applied to terms that contain only unused variables (ZeroSens, NormZero)
                     (S.Set a) ->                              -- the set of sensitive cols
                     (Map VarName a) ->                        -- input variable map
                     (Map VarName Expr) ->                     -- assigmnent variable map
                     Expr ->                                   -- the expression that we rewrite
                     (S.Set a, b)
processExpression s f nullify sensitiveCols inputMap asgnMap expr =
    let varNames = extractArgs expr in
    let usedInputVarNames = Data.List.filter (\x -> member (s ++ x) inputMap) varNames in
    let usedAsgnVarNames  = Data.List.filter (\x -> member x asgnMap)  varNames in


    let inputVars        = Data.List.map (\x -> inputMap ! (s ++ x))                                    usedInputVarNames in
    let asgnInputsExprs  = Data.List.map (matchAsgnVariable s f nullify sensitiveCols inputMap asgnMap) usedAsgnVarNames in

    let (asgnInputs,asgnExprs) = Data.List.unzip asgnInputsExprs in
    (S.union (S.fromList inputVars) (Data.List.foldr S.union S.empty asgnInputs), f expr inputVars asgnExprs asgnInputs)

--check if the variable is a keys in a map, apply processExpression to the value of that key
matchAsgnVariable :: (Show a, Ord a) => String -> (Expr -> [a] -> [b] -> [S.Set a] -> b) -> (b -> b) -> (S.Set a) -> (Map VarName a) -> (Map VarName Expr) -> VarName -> (S.Set a,b)
matchAsgnVariable s f nullify sensitiveCols inputMap asgnMap x =

        -- if y is an assignment variable, find its value recursively
        let expr = (asgnMap ! x) in
        let (expVars,e) = (processExpression s f nullify sensitiveCols inputMap asgnMap expr) in
        if S.null (S.intersection expVars sensitiveCols) then (S.empty, nullify e) else (expVars,e)

-- read the DB line by line -- no speacial parsing, assume that the delimiters are whitespaces
readInput :: String -> IO String
readInput path = do
   content <- readFile path
   return content

readDoubles :: String -> [[Double]]
readDoubles s = fmap (Data.List.map read . words) (lines s)

-- add the entire second argument to each query of the first argument list
mergeQueryFuns :: [Function] -> [Function] -> [Function]
mergeQueryFuns [] _ = []
mergeQueryFuns (F as b : qs1) qs2 =
    let as1 = concat $ Data.List.map (\(F as' _) -> toList as') qs2 in
    let as2 = Data.Map.fromList as1 in
    (F (Data.Map.union as as2) b) : (mergeQueryFuns qs1 qs2)

-- computes full query and filter expressions (as functions), updates the corresponding maps
processQuery :: Query -> (Map TableName [Function], Map TableName [Function]) -> (Map TableName [Function], Map TableName [Function])
processQuery (P outputName outputColNames queryFuns inputTableNames filters) (tableQueryMap,tableFilterMap) =

    --trace (show inputTableNames ++ "\n" ++ show tableQueryMap ++ "\n" ++ show tableFilterMap ++ "\n\n") $
   
    -- find the cross product query of all used input tables
    let inputQFuns      = concat $ Data.List.map (\x -> tableQueryMap ! x) inputTableNames in
    let inputFilters    = concat $ Data.List.map (\x -> tableFilterMap ! x) inputTableNames in

    let outputQueryFuns = mergeQueryFuns queryFuns inputQFuns in
    let outputFilters  = inputFilters  ++ mergeQueryFuns filters inputQFuns in

    (fromList $ (outputName, outputQueryFuns) : (toList tableQueryMap), fromList $ (outputName, outputFilters) : (toList tableFilterMap))

-- compute table data for a cross product
getTableCrossProductData :: [TableName] -> Map TableName TableData -> TableData
getTableCrossProductData tableNames tableMap =

    let allInputVars       = Data.List.map (\x -> getInputVars (tableMap ! x) ) tableNames in
    let allTables          = Data.List.map (\x -> getTableValues (tableMap ! x) ) tableNames in
    let allExprs           = Data.List.map (\x -> getExpr (tableMap ! x) ) tableNames in
    let allQFuns           = Data.List.map (\x -> getQFun (tableMap ! x) ) tableNames in
    let allDbNorms         = Data.List.map (\x -> getNorm (tableMap ! x) ) tableNames in
    let allDbSensitiveRows = Data.List.map (\x -> getSensitiveRows (tableMap ! x) ) tableNames in
    let allDbSensitiveVars = Data.List.map (\x -> getSensitiveCols (tableMap ! x) ) tableNames in

    -- the expressions are concatenated, since each of them describes a column
    let inputVars   = concat allInputVars in
    let exprs       = concat allExprs in
    let qFuns       = concat allQFuns in
    let dbNorms     = concat allDbNorms in
    let dbSensitiveVars = concat allDbSensitiveVars in

    -- find the cross product of all used tables
    let tableCrossProduct        = tableJoin allTables in
    let numsOfRows = Data.List.map length allTables in
    let sensitiveRowCrossProduct = charVecJoin $ zipWith charVec numsOfRows allDbSensitiveRows in
    let dbSensitiveRows = fromCharVec sensitiveRowCrossProduct in

    T tableCrossProduct inputVars exprs qFuns dbNorms dbSensitiveRows dbSensitiveVars


data TableData =
    -- content columnNames exprs norms aggrNorms sensRows sensCols
    T B.Table [VarName] [B.Expr] [Function] [(String,Function)] [Int] [VarName]
  deriving Show

getTableValues (T x _ _ _ _ _ _) = x 
getInputVars   (T _ x _ _ _ _ _) = x 
getExpr        (T _ _ x _ _ _ _) = x 
getQFun        (T _ _ _ x _ _ _) = x 
getNorm        (T _ _ _ _ x _ _) = x
getSensitiveRows (T _ _ _ _ _ x _) = x 
getSensitiveCols (T _ _ _ _ _ _ x) = x 

readAllTables :: Bool -> [TableName] -> IO (Map TableName TableData)
readAllTables usePrefices tableNames = do

    -- collect all tables and all column names that will be used in our query
    -- read table sensitivities from corresponding files
    -- mapM is a standard function [IO a] -> IO [a]
    let dbData     = mapM (\tableName -> readDB $ tableName ++ ".db") tableNames
    let dbNormData = mapM (\tableName -> parseFromFile norm $ tableName ++ ".nrm") tableNames

    (tableColNames, tableValues) <- fmap unzip dbData
    (tableSensitives,tableNormFuns)  <- fmap unzip dbNormData
    let (tableSensitiveRows,tableSensitiveVars) = unzip tableSensitives

    -- we put column names inside variables
    let namePrefices = Data.List.map (\tableName -> if usePrefices then tableName ++ "." else "") tableNames
    let taggedTableColNames = zipWith (\x ys -> Data.List.map (\y -> x ++ y) ys) namePrefices tableColNames
    let taggedSensitiveVars = zipWith (\x ys -> Data.List.map (\y -> x ++ y) ys) namePrefices tableSensitiveVars

    -- put all table data together
    let tableMap = processAllTables tableNames taggedTableColNames tableValues tableNormFuns taggedSensitiveVars tableSensitiveRows
    return (fromList tableMap)

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
    T tableValues inputVars exprs qFuns [(tableName, normFun)] dbSensitiveRows dbSensitiveVars


-- putting everything together
getBanachAnalyserInput :: String -> IO (B.Table, B.TableExpr)
getBanachAnalyserInput input = do

    -- "sqlQuery" parses a single query of the form SELECT ... FROM ... WHERE
    queries <- parseFromFile sqlQueries input
    let lastQuery = last queries 
    let usePrefices = True
    -- "query" parses the old format where the query function is computed line by line
    --lastQuery <- parseFromFile query input
    --let queries = [lastQuery]
    --let usePrefices = False

    -- collect all table names used by all queries, take those that should be read from input files
    let allTableNames = concat $ Data.List.map getQueryDbFileNames queries
    let intermTableNames = Data.List.map getQueryTableName queries
    let inputTableNames = S.toList $ S.difference (S.fromList allTableNames) (S.fromList intermTableNames)
    inputTableMap <- readAllTables usePrefices inputTableNames

    -- process all queries one by one, get the map that stores final query functions and filters
    let numOfInputTables = length inputTableNames
    let inputQueryMap  = fromList $ zip inputTableNames (replicate numOfInputTables [])
    let inputFilterMap = fromList $ zip inputTableNames (replicate numOfInputTables [])

    let (queryMap, filterMap) = Data.List.foldl (\x y -> processQuery y x) (inputQueryMap,inputFilterMap) queries
    --putStrLn $ Data.List.foldr (\(tableName, x) y -> "TableQ " ++ tableName ++ ": " ++ show x ++ "\n\n" ++ y) "" (toList queryMap)
    --putStrLn $ Data.List.foldr (\(tableName, x) y -> "TableF " ++ tableName ++ ": " ++ show x ++ "\n\n" ++ y) "" (toList filterMap)

    -- we assume that each input table is used only once, so we take the table cross product as an input
    let (T inputTable inputVars _ _ dbNormData dbSensitiveRows dbSensitiveVars) = getTableCrossProductData inputTableNames inputTableMap
    let numOfRows = length inputTable
    let inputVarList = zip inputVars [0..length inputVars - 1]
    let inputMap = fromList inputVarList
    let dbSensitiveCols = Data.List.map (\x -> inputMap ! x) dbSensitiveVars
    let dbSensitiveRowsCV = charVec numOfRows dbSensitiveRows

    putStrLn $ "----------------"
    putStrLn $ "All input variables:    " ++ show (toList inputMap)
    putStrLn $ "All sensitive cols:     " ++ show dbSensitiveCols

    -- we assume that the final table has one column (in theory, there can be more)
    let lastQueryFunsNofilter  = queryMap ! "output"
    let lastQueryExprsNofilter = Data.List.map (\x -> snd $ query2Expr dbSensitiveVars inputMap x) lastQueryFunsNofilter

    putStrLn $ "----------------"
    --putStrLn $ "Query Funs  Nofilter: " ++ show lastQueryFunsNofilter
    putStrLn $ "Query Exprs Nofilter: " ++ show lastQueryExprsNofilter

    -- we may now apply the filter
    let filterFuns = filterMap ! "output"
    let (filterVars, filterExprs) = unzip $ Data.List.map (query2Expr dbSensitiveVars inputMap) filterFuns
    let filterValues = Data.List.map (\x -> Data.List.map B.fx $ zipWith B.analyzeExpr inputTable (replicate numOfRows x)) filterExprs

    putStrLn $ "----------------"
    --putStrLn $ "All filter Funs: " ++ show filterFuns
    putStrLn $ "All filterVars:  " ++ show filterVars
    putStrLn $ "All filterExprs: " ++ show filterExprs
    putStrLn $ "----------------"

    -- TODO this is CHEATING!
    -- thoretically, the best value for 'infinity' is the maximum absolute value amongst those that we aggregate
    -- however, this is a bad idea since it depends on private data and has some sensitivity by itself; we want it to be a constant
    let infVal = B.fx $ B.analyzeTableExpr inputTable (B.SelectMax (Data.List.map (\expr -> B.ComposeL 1.0 [expr]) lastQueryExprsNofilter))
    --let infVal = 10000.0 -- this is more honest, but it gives very bad sensitivities

    let dbSensitiveColSet = S.fromList dbSensitiveCols
    let (lastQueryFuns, (filtSensitiveRowsCV, table)) = applyFilters infVal lastQueryFunsNofilter inputTable dbSensitiveRowsCV inputMap filterFuns filterVars filterValues
    let numOfFiltRows = length table

    -- now transform the query to a banach expression
    let lastQueryFun = last lastQueryFuns
    let lastQueryExpr = snd $ query2Expr dbSensitiveVars inputMap lastQueryFun
    let lastQueryAggr = queryExprAggregate numOfFiltRows filtSensitiveRowsCV lastQueryFun lastQueryExpr

    --putStrLn $ "Query function:     " ++ show lastQueryFun
    putStrLn $ "Query expression with filter:   " ++ show lastQueryExpr
    putStrLn $ "Query num of rows after filtering:   " ++ show numOfFiltRows
    --putStrLn $ "Query filtSensitiveRowsCV:   " ++ show filtSensitiveRowsCV
    putStrLn $ "Query aggr expression:   " ++ show lastQueryAggr

    -- the aggregation norm is equalized, and it is chosen to be the finest one if they are different
    let (dbNormTableNames, dbNormFuns) = unzip dbNormData
    let namePrefices = Data.List.map (\tableName -> if usePrefices then tableName ++ "." else "") dbNormTableNames
    let (dbNorms,dbAggrNorms) = unzip $ zipWith (\x y -> norm2Expr x dbSensitiveVars inputMap y) namePrefices dbNormFuns

    let dbNorm     = NormL (Exactly 1.0) dbNorms
    let dbAggrNorm = Data.List.foldr takeFiner (Exactly 1.0) dbAggrNorms

    -- here 'snd inputVarList' means that the variables are integes
    -- 'fst' would be VarNames, which are useful for testing (if use them, then use them also in the dbNorm)
    let queryNorm     = deriveNorm (Data.List.map snd inputVarList) lastQueryExpr
    let queryAggrNorm = deriveTableNorm lastQueryAggr

    putStrLn $ "----------------"
    putStrLn $ "database norm       = Rows: " ++ show dbAggrNorm ++ " | Cols: " ++ show dbNorm
    putStrLn $ "query norm          = Rows: " ++ show queryAggrNorm ++ " | Cols: " ++ show queryNorm
    --putStrLn $ "normalized database columns norm = " ++ show (normalizeNorm dbNorm)
    --putStrLn $ "normalized query    columns norm = " ++ show (normalizeNorm queryNorm)

    -- adjust the query norm to the table norm
    let newNorm = normalizeAndVerify queryNorm dbNorm
    let adjustedExpr = case newNorm of
            Just norm -> let (mapCol,mapLN) = extractScalings norm in updateExpr mapCol mapLN lastQueryExpr
            Nothing -> lastQueryExpr

    let adjustedAggrExpr = case newNorm of
            Just norm -> let (mapCol,mapLN) = extractScalings norm in updateTableExpr lastQueryAggr mapCol mapLN queryAggrNorm dbAggrNorm numOfRows
            Nothing -> lastQueryAggr

    let newQueryNorm = deriveNorm (Data.List.map snd inputVarList) adjustedExpr
    let newAggrNorm  = deriveTableNorm adjustedAggrExpr

    putStrLn $ "adjusted query norm = Rows: " ++ show newAggrNorm ++ " | Cols: "  ++ show newQueryNorm
    putStrLn $ "----------------"
    putStrLn $ "variable norm scaling: " ++ case newNorm of {Nothing -> "???\n"; Just norm -> show (extractScalings norm) ++ "\n"}

    putStrLn $ case newNorm of
            Just _  -> "OK: the database norm is at least as large as the query norm."
            Nothing -> "WARNING: could not prove that the database norm is at least as large as the query norm."

    putStrLn $ "----------------"
    putStrLn $ "table = " ++ show table ++ "\n"
    putStrLn $ "initial expr = " ++ show lastQueryAggr ++ "\n"
    putStrLn $ "adjusted expr = " ++ show adjustedAggrExpr
    putStrLn $ "----------------"
    return (table,adjustedAggrExpr)


