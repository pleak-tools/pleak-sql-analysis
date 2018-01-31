module Parser where

import System.Environment
import System.IO.Unsafe

-- some Megaparsec-specific modules
import Text.Megaparsec
import Text.Megaparsec.Expr
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
--
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

---------------------------------------------------------------------------------------------
-- TODO: parsing of 'expr' and 'tableExpr' is being synchronized with B.Expr and B.TableExpr

-- keywords
allKeyWords :: [String] -- list of reserved "words"
allKeyWords = ["return",
               "^","LN","exp","sqrt","root","scaleNorm","zeroSens","lp","linf","prod","inv","div","min","max","sigmoid",
               "selectMin","selectMax","selectProd","selectL",
               "SELECT","FROM","WHERE","AND"]

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

-- a norm expression
normExpr :: VarName -> Parser [Expr]
normExpr _ = scaleNormExpr
  <|> zeroSensExpr
  <|> lpNormExpr
  <|> linfNormExpr
  <|> lnExpr

-- parsing different expressions, one by one
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

scaleAExpr :: Parser (AExpr a -> AExpr a)
scaleAExpr = do
  c <- signedFloat
  symbol "*"
  return (AUnary (AScale c))

aExpr :: Parser (AExpr VarName)
aExpr = makeExprParser aTerm aOperators

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
  <|> Var <$> varName


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

selectCountAExpr :: Parser (VarName -> TableExpr)
selectCountAExpr = do
  keyWord "COUNT"
  return SelectCount

selectAExpr :: Parser (VarName -> TableExpr)
selectAExpr = do
  return Select

filterVarConst :: Parser (Filter VarName)
filterVarConst = do
  x <- varName
  op <- order
  c <- signedFloat
  return (VarConst op x c)

filterVarVar :: Parser (Filter VarName)
filterVarVar = do
  x <- varName
  op <- order
  y <- varName
  return (VarVar op x y)


-- ======================================================================= --
-----------------------------------------------------------------------------
----      The code below does not need to be updated with Banach.hs      ----
-----------------------------------------------------------------------------
sqlFilter :: Parser (Filter VarName)
sqlFilter = try filterVarConst <|> filterVarVar

sqlQuery :: Parser Query
sqlQuery = do
  keyWord "SELECT"
  g <- sqlAggregator
  aexpr <- aExpr
  let y = "y~"
  keyWord "FROM"
  tablePaths <- sepBy1 identifier (symbol ",")
  filters    <- sqlQueryFilter
  let as = aexprToExpr y (aexprNormalize $ aexpr)
  let b  = g y
  return (P (F as b) tablePaths filters)

sqlQueryFilter :: Parser [Filter VarName]
sqlQueryFilter = sqlQueryWithFilter <|> sqlQueryWithoutFilter

sqlQueryWithoutFilter :: Parser [Filter VarName]
sqlQueryWithoutFilter = do
  return []

sqlQueryWithFilter :: Parser [Filter VarName]
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
  return (P f [tablePath] [])

-- the first row in the norm file is the list of sensitive rows
-- the second row in the norm file is the list of sensitive columns
norm :: Parser (([Int], [VarName]), Function)
norm = do
  is <- many integer
  xs <- many varName
  void (delim)
  f <- function NormParsing
  return ((is, xs), f)

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
    <|> C.alphaNumChar

-- we need to read string identifiers and afterwards map them to integers
varName :: Parser VarName
varName = identifier <|> constant

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

getQueryDbFileNames :: Query -> [String]
getQueryDbFileNames (P _ dbFileNames _) = dbFileNames

getQueryFilters :: Query -> [Filter VarName]
getQueryFilters (P _ _ filters) = filters

getQueryFunction :: Query -> Function
getQueryFunction (P f _ _) = f

getQueryConstants :: Query -> [String]
getQueryConstants (P (F as _) _ _) = 
    let cs = extractConstants $ elems as in
    -- remove repetitions by transforming the list to set and then back from set to list
    S.toList (S.fromList cs)

query2Expr :: Int -> [VarName] -> [Bool] -> (Map VarName B.Var) -> Function -> Either [B.Expr] B.TableExpr
query2Expr numOfRows sensitiveVars sensitiveRowsCV inputMap (F asgnMap y) =
    let x = extractArg y in
    let sensitiveCols = S.fromList (Data.List.map (\x -> inputMap ! x) sensitiveVars) in
    let (_,z) = matchAsgnVariable "" queryExpression B.ZeroSens sensitiveCols inputMap asgnMap x in
    -- the parameter 0 denotes that the indexation starts from 0
    let zs = zipWith (\x y -> if x then y else B.ZeroSens y) sensitiveRowsCV (replicate numOfRows z) in
    queryArg y zs

norm2Expr :: String -> Int -> [VarName] -> [Int] -> (Map VarName B.Var) -> Function -> (Norm B.Var, ADouble)
norm2Expr prefix numOfRows sensitiveVars sensitiveRows inputMap (F asgnMap y) =
    let x = extractArg y in
    let sensitiveCols = S.fromList (Data.List.map (\x -> inputMap ! x) sensitiveVars) in
    let (_,z) = matchAsgnVariable prefix normExpression NormZero sensitiveCols inputMap asgnMap x in
    (z, normArg y)

processExpression :: (Show a, Ord a) => 
                     String ->                                 -- the name of the database file that we prepend to all variable names
                     (Expr -> [a] -> [b] -> [S.Set a] -> b) -> -- the function that actually rewrites the term
                     (b -> b) ->                               -- applied to terms that contain only unused variables (ZeroSens, NormZero)
                     (S.Set a) ->                              -- the set of used variables
                     (Map VarName a) ->                        -- input variable map
                     (Map VarName Expr) ->                     -- assigmnent variable map
                     Expr ->                                   -- the expression that we rewrite
                     (S.Set a, b)
processExpression s f nullify usedVars inputMap asgnMap expr =
    let varNames = extractArgs expr in
    let usedInputVarNames = Data.List.filter (\x -> member (s ++ x) inputMap) varNames in
    let usedAsgnVarNames  = Data.List.filter (\x -> member x asgnMap)  varNames in

    let inputVars       = Data.List.map (matchInputVariable s inputMap)                           usedInputVarNames in
    let asgnInputsExprs = Data.List.map (matchAsgnVariable s f nullify usedVars inputMap asgnMap) usedAsgnVarNames  in

    let (asgnInputs,asgnExprs) = Data.List.unzip asgnInputsExprs in
    (S.union (S.fromList inputVars) (Data.List.foldr S.union S.empty asgnInputs), f expr inputVars asgnExprs asgnInputs)

--check if the variable is a keys in a map, return the corresponding value if it is
matchInputVariable :: (Show a, Ord a) => String -> (Map VarName a) -> VarName -> a
matchInputVariable s inputMap x = (inputMap ! (s ++ x))

--check if the variable is a keys in a map, apply processExpression to the value of that key
matchAsgnVariable :: (Show a, Ord a) => String -> (Expr -> [a] -> [b] -> [S.Set a] -> b) -> (b -> b) -> (S.Set a) -> (Map VarName a) -> (Map VarName Expr) -> VarName -> (S.Set a,b)
matchAsgnVariable s f nullify usedVars inputMap asgnMap x =

        -- if y is an assignment variable, find its value recursively
        let expr = (asgnMap ! x) in
        let (expVars,e) = (processExpression s f nullify usedVars inputMap asgnMap expr) in
        if S.null (S.intersection expVars usedVars) then (S.empty, nullify e) else (expVars,e)

-- read the DB line by line -- no speacial parsing, assume that the delimiters are whitespaces
readInput :: String -> IO String
readInput path = do
   content <- readFile path
   return content

readDoubles :: String -> [[Double]]
readDoubles s = fmap (Data.List.map read . words) (lines s)

-- putting everything together
getBanachAnalyserInput :: String -> IO (B.Table, B.TableExpr)
getBanachAnalyserInput input = do

    -- "sqlQuery" parses a single query of the form SELECT ... FROM ... WHERE
    -- "query" parses the old format where the query function is computed line by line
    queryPr <- parseFromFile sqlQuery input
    --queryPr  <- parseFromFile query input

    let tableNames = getQueryDbFileNames queryPr
    let filters    = getQueryFilters queryPr
    let queryFun   = getQueryFunction queryPr

    -- collect all tables and all column names that will be used in our query
    -- mapM is a standard function [IO a] -> IO [a]
    let dbData = mapM (\tableName -> readDB $ tableName ++ ".db") tableNames
    (allInputVars, allTables) <- fmap unzip dbData

    -- if we have several tables, we want to add prefices to variables to distinguish them if the names repeat
    let namePrefices = if length tableNames > 1 then Data.List.map (\tableName -> tableName ++ ".") tableNames else (replicate (length tableNames) "")

    -- fix an integer index for each variable name
    -- we assume that the table name is used as a prefix to each column name
    -- the constants are treated as special non-sensitive variables
    let inputVars = concat $ zipWith (\namePrefix xs -> Data.List.map (\x -> namePrefix ++ x) xs) namePrefices allInputVars
    let constVars = getQueryConstants queryPr
    let inputVarList = zip (inputVars ++ constVars) [0..length inputVars + length constVars - 1]
    putStrLn $ "All input variables: " ++ show inputVars
    putStrLn $ "All constants: " ++ show constVars
    putStrLn $ "All filters: " ++ show filters ++ "\n"
    let inputMap = fromList inputVarList

    -- read table sensitivities from corresponding files
    let numsOfRows = Data.List.map length allTables
    let dbNormData = mapM (\tableName -> parseFromFile norm $ tableName ++ ".nrm") tableNames
    (allDbSensitives,allDbNorms) <- fmap unzip dbNormData
    let (allDbSensitiveRows,allDbSensitiveVars) = unzip allDbSensitives

    let dbSensitiveVars = concat $ zipWith (\namePrefix xs -> Data.List.map (\x -> namePrefix ++ x) xs) namePrefices allDbSensitiveVars
    let dbSensitiveCols = Data.List.map (\x -> inputMap ! x) dbSensitiveVars

    -- find the cross product of all used tables
    let tableCrossProduct        = tableJoin allTables
    let sensitiveRowCrossProduct = charVecJoin $ zipWith charVec numsOfRows allDbSensitiveRows
    let numOfCrossProdRows       = length tableCrossProduct

    -- add dummy columns that will represent the constants used by our query
    let sensitiveVarSet = S.fromList dbSensitiveVars
    let tableWithConstantCols = transpose $ (transpose tableCrossProduct) ++ 
                                            (Data.List.map (\x -> replicate numOfCrossProdRows (read (snd $ splitAt 5 x) :: Double)) constVars)

    -- now apply the filters (filter by non-sensitive conditions directly, and use sigmoids for sensitive conditions)
    let (filteredQuery, (dbSensitiveRowsCV, table)) = applyFilters queryFun tableWithConstantCols sensitiveRowCrossProduct sensitiveVarSet inputMap filters
    let dbSensitiveRows = fromCharVec dbSensitiveRowsCV
    let numOfRows = length table

    -- this is output about the cross product table
    putStrLn $ "Sensitive rows of the table: " ++ show dbSensitiveRows
    putStrLn $ "Sensitive cols of the table: " ++ show dbSensitiveCols ++ "\n"

    -- the crossproduct table norm is by default an l1-norm of their columns
    -- the aggregation norm is equalized, and it is chosen to be the finest one if they are different
    let (dbNorms,dbAggrNorms) = unzip $ zipWith (\x y -> norm2Expr x numOfRows dbSensitiveVars dbSensitiveRows inputMap y) namePrefices allDbNorms
    let dbNorm     = NormL (Exactly 1.0) dbNorms
    let dbAggrNorm = Data.List.foldr takeFiner (Exactly 1.0) dbAggrNorms
    putStrLn $ "database norm = Rows: " ++ show dbAggrNorm ++ " | Cols: " ++ show dbNorm

    -- the parser currently allows SELECT queries without aggregation function, but we do not process such queries yet
    -- Left means that there is no aggregation, and Right means that there is one
    let exprs = query2Expr numOfRows dbSensitiveVars dbSensitiveRowsCV inputMap filteredQuery
    let (queryNorm, queryAggrNorm) = case exprs of {Left _ -> error ("The final operation should be an aggregation"); Right e -> deriveTableNorm (Data.List.map snd inputVarList) e}
    let expr                       = case exprs of {Left _ -> error ("The final operation should be an aggregation"); Right e -> e}

    putStrLn $ "query norm    = Rows: " ++ show queryAggrNorm ++ " | Cols: " ++ show queryNorm
    putStrLn $ "normalized database columns norm = " ++ show (normalizeNorm dbNorm)
    putStrLn $ "normalized query    columns norm = " ++ show (normalizeNorm queryNorm)

    let newNorm = normalizeAndVerify queryAggrNorm dbAggrNorm queryNorm dbNorm
    let adjustedExpr = case newNorm of
            Just norm -> updateTableExpr expr norm
            Nothing -> expr

    let (newQueryNorm, newAggrNorm) = deriveTableNorm (Data.List.map snd inputVarList) adjustedExpr
    putStrLn $ "adjusted query norm = " ++ show newQueryNorm
    putStrLn $ "variable norm scaling: " ++ case newNorm of {Nothing -> "???\n"; Just norm -> show (extractScalings norm) ++ "\n"}

    putStrLn $ case newNorm of
            Just _  -> "OK: the database norm is at least as large as the query norm."
            Nothing -> "WARNING: could not prove that the database norm is at least as large as the query norm."

    putStrLn $ "----------------"
    putStrLn $ "table = " ++ show table ++ "\n"
    putStrLn $ "initial expr = " ++ show expr ++ "\n"
    putStrLn $ "adjusted expr = " ++ show adjustedExpr
    putStrLn $ "----------------"
    --let ns = [NormL (Exactly 1.0) [Col "x1"], NormL (Exactly 2.0) [Col "x2"], NormL (Exactly 3.0) [Col "x3"], NormL (Exactly 1.0) [Col "x4"], NormL (Exactly 2.0) [Col "x5"]]
    --let n1 = NormLInf ns
    --let n2 = NormLInf [NormL (Exactly 1.0) [Col "x1", Col "x4"], NormL (Exactly 2.0) [Col "x2", Col "x5"], NormL (Exactly 3.0) [Col "x3"]]
    --let n1 = NormL (Exactly 6.0) [Col "x", Col "z"]
    --let n2 = NormL (Exactly 7.0) [NormL (Exactly 5.0) [Col "x", Col "z"], Col "y"]
    --let n1 = NormScale 0.5 (NormL (Exactly 9.0) [Col "x", Col "z"])
    --let n2 = NormL (Exactly 7.0) [NormL (Exactly 5.0) [NormScale 10.0 (Col "x"), Col "z"], Col "y"]
    --putStrLn $ show n1
    --putStrLn $ show n2
    --putStrLn $ show (normalizeAndVerify n1 n2)
    --putStrLn $ show (rearrangeNorm Group LT Any ns)
    --putStrLn $ show (rearrangeNorm Group LT (Exactly 2.0) ns)
    --putStrLn $ show (rearrangeNorm Group LT (Exactly 3.0) ns)
    return (table,adjustedExpr)


