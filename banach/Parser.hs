module Parser where

import System.Environment
import System.IO.Unsafe

-- some Megaparsec-specific modules
import Text.Megaparsec
import Text.Megaparsec.Expr
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
--
import Debug.Trace
import Control.Monad (void)
import Data.Either
import Data.List
import Data.Map
import Data.Void

-- import Expr directly from Banach.hs, 'qualified' because we want to reuse the names
import qualified Banach as B

-- let the variable names be alphanumeric strings starting with a character
type VarName = String

-----------------------------------------------------------------------------------
-- TODO: Expr and TableExpr are being synchronized with B.Expr and B.TableExpr

-- these are single-step Banach expressions, all 'Expr' and 'Var' substituted with 'VarName'
data Expr = Power VarName Double      -- x^r with norm | |
          | PowerLN VarName Double    -- x^r with logarithmic norm: ||x|| = |ln x|, addition in Banach space is multiplication of real numbers
          | Exp Double VarName        -- e^(r*x) with norm | |
          | ScaleNorm Double VarName  -- E with norm a * N
          | ZeroSens VarName          -- E with sensitivity forced to zero (the same as ScaleNorm with a -> infinity)
          | L Double [VarName]        -- ||(x1,...,xn)||_p with l_q-norm where q = p/(p-1)
          | LInf [VarName]            -- same with p = infinity, q = 1
          | Prod [VarName]            -- E1*...*En with norm ||(N1,...,Nn)||_1
          | Min [VarName]             -- min{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
          | Max [VarName]             -- max{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
  deriving Show

-- expressions of type TableExpr use values from the whole table
data TableExpr = SelectProd VarName        -- product (map E rows) with norm ||(N1,...,Nn)||_1 where Ni is N applied to ith row
               | SelectMin VarName         -- min (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]
               | SelectMax VarName         -- max (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]
  deriving Show


-----------------------------------------------------------------------------------
-- TODO: reconstruction of terms are being synchronized with B.Expr and B.TableExpr

extractArg :: TableExpr -> VarName
extractArg t =
    case t of
        SelectProd x -> x
        SelectMin x  -> x
        SelectMax x  -> x

substituteArg :: TableExpr -> B.Expr -> B.TableExpr
substituteArg t y =
    case t of
        SelectProd _ -> B.SelectProd y
        SelectMin _  -> B.SelectMin y
        SelectMax _  -> B.SelectMax y

-- Expr constructor arguments can be Var, Expr, Double -- let us split these types into triples ([Var],[Expr],[Double])
extractArgs :: Expr -> ([VarName],[VarName],[Double])
extractArgs t =
    case t of
        Power x c     -> ([x],[],[c])
        PowerLN x c   -> ([x],[],[c])
        Exp c x       -> ([x],[],[c])
        ScaleNorm c x -> ([],[x],[c])
        ZeroSens x    -> ([],[x],[])
        L c xs        -> (xs,[],[c])
        LInf xs       -> (xs,[],[])
        Prod xs       -> ([],xs,[])
        Min xs        -> ([],xs,[])
        Max xs        -> ([],xs,[])

substituteArgs :: Expr -> [B.Var] -> [B.Expr] -> [Double] -> B.Expr
substituteArgs t xs es cs =
    case t of
        Power _ _     -> B.Power (head xs) (head cs)
        PowerLN _ _   -> B.PowerLN (head xs) (head cs)
        Exp _ _       -> B.Exp (head cs) (head xs)
        ScaleNorm _ _ -> B.ScaleNorm (head cs) (head es)
        ZeroSens _    -> B.ZeroSens (head es)
        L _ _         -> B.L (head cs) xs
        LInf _        -> B.LInf xs
        Prod _        -> B.Prod es
        Min _         -> B.Min es
        Max _         -> B.Max es

---------------------------------------------------------------------------------------------
-- TODO: parsing of 'expr' and 'tableExpr' is being synchronized with B.Expr and B.TableExpr

-- keywords
allKeyWords :: [String] -- list of reserved "words"
allKeyWords = ["return","^","LN","exp","scaleNorm","zeroSens","lp","linf","prod","min","max","selectMin","selectMax","selectProd"]

-- an expression
expr :: Parser Expr
expr = powerExpr
  <|> powerLNExpr
  <|> expExpr
  <|> scaleNormExpr
  <|> zeroSensExpr
  <|> lpNormExpr
  <|> linfNormExpr
  <|> prodExpr
  <|> minExpr
  <|> maxExpr

-- parsing different expressions, one by one
powerExpr :: Parser Expr
powerExpr = do
  keyWord "^"
  a <- varName
  b <- float
  return (Power a b)

powerLNExpr :: Parser Expr
powerLNExpr = do
  keyWord "LN"
  keyWord "^"
  a <- varName
  b <- signedFloat
  return (PowerLN a b)

expExpr :: Parser Expr
expExpr = do
  keyWord "exp"
  a <- signedFloat
  b <- varName
  return (Exp a b)

scaleNormExpr :: Parser Expr
scaleNormExpr = do
  keyWord "scaleNorm"
  a <- float
  b <- varName
  return (ScaleNorm a b)

zeroSensExpr :: Parser Expr
zeroSensExpr = do
  keyWord "zeroSens"
  a <- varName
  return (ZeroSens a)

lpNormExpr :: Parser Expr
lpNormExpr = do
  keyWord "lp"
  a  <- float
  bs <- many varName
  return (L a bs)

linfNormExpr :: Parser Expr
linfNormExpr = do
  keyWord "linf"
  bs <- many varName
  return (LInf bs)

prodExpr :: Parser Expr
prodExpr = do
  keyWord "prod"
  bs <- many varName
  return (Prod bs)

minExpr :: Parser Expr
minExpr = do
  keyWord "min"
  bs <- many varName
  return (Min bs)

maxExpr :: Parser Expr
maxExpr = do
  keyWord "max"
  bs <- many varName
  return (Max bs)

-- a table expression
tableExpr :: Parser TableExpr
tableExpr = selectProdExpr
  <|> selectMinExpr
  <|> selectMaxExpr

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



-- ======================================================================= --
-----------------------------------------------------------------------------
----      The code below does not need to be updated with Banach.hs      ----
-----------------------------------------------------------------------------

------------------------------------
---- Additional data structures ----
------------------------------------

-- the format of the input file
--   "String" is the name of the database file
--   "Map VarName Int" maps variable names to unique integers -- their column indices in the database
--                     we assume that the inputs listed in the input file are ordered as the columns
--   "Function" is the function on inputs that the inquirer wants to compute
data Program
  = P String (Map VarName Int) Function
  deriving (Show)

-- a function consists of unit expression assignments "Map VarName Expr" and returns a single "TableExpr"
-- an assigment is identitified by the assigned variable, we assume the variables are not reused
-- each assignment maps a variable to an expression
data Function
  = F (Map VarName Expr) TableExpr
  deriving (Show)

-- Define the parser type
-- 'Void' means 'no custom error messages'
-- 'String' means 'input comes in form of a String'
type Parser = Parsec Void String

--------------------------------------
---- Parsing general input format ----
--------------------------------------

program :: Parser Program
program = do
  tablePath <- text
  void (delim)
  xs <- many varName
  void (delim)
  f <- function
  return (P tablePath (fromList (zipWith (\x y -> (x,y)) xs [0..((length xs) - 1)])) f)

asgnStmt :: Parser (VarName,Expr)
asgnStmt = do
  a  <- varName
  void (asgn)
  b <- expr
  void (delim)
  return (a,b)

returnStmt :: Parser TableExpr
returnStmt = do
  keyWord "return"
  a <- tableExpr
  void (delim)
  return a

function :: Parser Function
function = do
  as <- many asgnStmt
  b  <- returnStmt
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
    p       = (:) <$> C.letterChar <*> many C.alphaNumChar
    check x = if elem x allKeyWords
              then fail $ "keyword " ++ show x ++ " cannot be an identifier"
              else return x

-- we need to read string identifiers and afterwards map them to integers!
varName :: Parser VarName
varName = identifier

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


-------------------------------------------------------
---- Converting a Program to Banach Analyser input ----
-------------------------------------------------------

-- read the database from the file defined in the program string
-- read is as a single table row
program2DB :: IO Program -> IO B.Table
program2DB io_program = do
    (P dbFileName _ _)  <- io_program
    table <- fmap readDoubles (readInput dbFileName)
    return table

program2Expr :: Program -> B.TableExpr
program2Expr (P _ var_map (F asgn_map y)) =
    let x = extractArg y in
    let z = matchIntermVariable var_map asgn_map x in
    substituteArg y z

processExpression :: (Map VarName Int) -> (Map VarName Expr) -> Expr -> B.Expr 
processExpression var_map asgn_map expr =
    let (xs,es,cs) = extractArgs expr in
    let new_xs = fmap (matchColumnVariable var_map)          xs in
    let new_es = fmap (matchIntermVariable var_map asgn_map) es in
    substituteArgs expr new_xs new_es cs

--check if the variable is a keys in a map, return the corresponding value if it is
matchColumnVariable :: (Map VarName a) -> VarName -> a
matchColumnVariable dict y =
    if member y dict then (dict ! y) else
    error ("Undefined column variable " ++ y)

--check if the variable is a keys in a map, apply processExpression to the value of that key
matchIntermVariable :: (Map VarName Int) -> (Map VarName Expr) -> VarName -> B.Expr
matchIntermVariable var_map asgn_map y =
    if member y asgn_map then processExpression var_map asgn_map (asgn_map ! y) else
    error ("Undefined intermediate variable " ++ y)

-- read the DB line by line -- no speacial parsing, assume that the delimiters are whitespaces
readInput path = do
   content <- readFile path
   return content

readDoubles :: String -> [[Double]]
readDoubles s = fmap (Data.List.map read . words) (lines s)

-- putting everything together
getBanachAnalyserInput :: String -> IO (B.Table, B.TableExpr)
getBanachAnalyserInput inputFile = do
    let iopr = parseFromFile program inputFile
    pr <- iopr
    table <- program2DB iopr
    let expr = program2Expr pr
    return (table,expr)

program2BanachAnalyserInput :: String -> IO B.AnalysisResult
program2BanachAnalyserInput inputFile = do
    (table,expr) <- getBanachAnalyserInput inputFile
    return (B.analyzeTableExpr table expr)

-- this should be called from outside
--main :: IO B.AnalysisResult
--main = do
--    input <- fmap head getArgs
--    program2BanachAnalyserInput input

