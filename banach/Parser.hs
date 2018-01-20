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
import qualified Data.Set as S
import Data.Void

-- import Expr directly from Banach.hs, 'qualified' because we want to reuse the names
import qualified Banach as B
import Norms

-- let the variable names be alphanumeric strings starting with a character
type VarName = String

-----------------------------------------------------------------------------------
-- TODO: Expr and TableExpr are being synchronized with B.Expr and B.TableExpr

-- these are single-step Banach expressions, all 'Expr' and 'Var' substituted with 'VarName'
data Expr = Power VarName Double        -- x^r with norm | |
          | PowerLN VarName Double    -- x^r with logarithmic norm: ||x|| = |ln x|, addition in Banach space is multiplication of real numbers
          | ComposePower VarName Double -- E^r with norm N
          | Exp Double VarName          -- e^(r*x) with norm | |
          | ScaleNorm Double VarName    -- E with norm a * N
          | ZeroSens VarName            -- E with sensitivity forced to zero (the same as ScaleNorm with a -> infinity)
          | L Double [VarName]          -- ||(x1,...,xn)||_p with l_q-norm where q = p/(p-1)
          | ComposeL Double [VarName]   -- ||(E1,...,En)||_p with norm ||(N1,...,Nn)||_p
          | LInf [VarName]              -- same with p = infinity, q = 1
          | Prod [VarName]              -- E1*...*En with norm ||(N1,...,Nn)||_1
          | Min [VarName]               -- min{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
          | Max [VarName]               -- max{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
  deriving Show

-- expressions of type TableExpr use values from the whole table
data TableExpr = SelectProd VarName        -- product (map E rows) with norm ||(N1,...,Nn)||_1 where Ni is N applied to ith row
               | SelectMin VarName         -- min (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]
               | SelectMax VarName         -- max (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]
               | SelectL Double VarName    -- ||(E1,...,En)||_p with norm ||(N1,...,Nn)||_p
  deriving Show

-- a small bit, denoting whether we are parsin a query or a norm
-- we define it, since a query and a norm have very similar format
data ParserInstance = QueryParsing | NormParsing

-----------------------------------------------------------------------------------
-- TODO: reconstruction of terms are being synchronized with B.Expr and B.TableExpr

extractArg :: TableExpr -> VarName
extractArg t =
    case t of
        SelectProd x -> x
        SelectMin x  -> x
        SelectMax x  -> x
        SelectL _ x  -> x

queryArg :: TableExpr -> B.Expr -> B.TableExpr
queryArg t y =
    case t of
        SelectProd _ -> B.SelectProd y
        SelectMin _  -> B.SelectMin y
        SelectMax _  -> B.SelectMax y
        SelectL c _  -> B.SelectL c y

normArg :: TableExpr -> Norm a -> Norm a
normArg t y =
    case t of
        SelectProd _ -> NormLInf [y]
        SelectMin _  -> NormLInf [y]
        SelectMax _  -> NormLInf [y]
        SelectL c _  -> NormL (AtMost c) [y]

-- Expr constructor variable arguments can be Var, Expr
-- we put all of them into one list and later check whether a variable is an input or an assignment variable
extractArgs :: Expr -> [VarName]
extractArgs t =
    case t of
        Power x _        -> [x]
        PowerLN x _      -> [x]
        Exp _ x          -> [x]
        ScaleNorm _ x    -> [x]
        ZeroSens x       -> [x]
        L _ xs           -> xs
        LInf xs          -> xs
        Prod xs          -> xs
        Min xs           -> xs
        Max xs           -> xs

-- this is needed to make error of a missing head clearer
-- the errors come where the argument has to be an input variable, but it is actually an expression, and vice versa
headInputVar :: Expr -> [a] -> a
headInputVar t [] = error ("Cannot substitude variables into " ++ show t ++ ",\n the arguments are not of Var (input variable) type")
headInputVar t xs = head xs

headAsgnVar :: Expr -> [a] -> a
headAsgnVar t [] = error ("Cannot substitude variables into " ++ show t ++ ",\n the arguments are not of Expr (assignment variable) type")
headAsgnVar t xs = head xs

onlyInputVars :: Expr -> [a] -> [b] -> [a]
onlyInputVars t [] _ = error ("Cannot substitude variables into " ++ show t ++ ",\n the arguments are not of Var (input variable) type")
onlyInputVars t xs [] = xs
onlyInputVars t _ _ = error ("Cannot substitude variables into " ++ show t ++ ",\n some arguments are not of Var (input variable) type")

onlyAsgnVars :: Expr -> [a] -> [b] -> [b]
onlyAsgnVars t _ [] = error ("Cannot substitude variables into " ++ show t ++ ",\n the arguments are not of Expr (assignment variable) type")
onlyAsgnVars t [] xs = xs
onlyAsgnVars t _ _ = error ("Cannot substitude variables into " ++ show t ++ ",\n some arguments are not of Expr (assignment variable) type")

-- the constructor may depend on whether the arguments are input variables or expressions
queryExpression :: Expr -> [B.Var] -> [B.Expr] -> B.Expr
queryExpression t xs es =
    case t of
        Power _ c        -> if xs /= [] then
                                B.Power (headInputVar t xs) c
                            else
                                B.ComposePower (headAsgnVar t es) c
        PowerLN _ c      -> B.PowerLN (headInputVar t xs) c
        Exp c _          -> B.Exp c (headInputVar t xs)
        ScaleNorm c _    -> B.ScaleNorm c (headAsgnVar t es)
        ZeroSens _       -> B.ZeroSens (headAsgnVar t es)
        L c _            -> if xs /= [] then
                                B.L c (onlyInputVars t xs es)
                            else
                                B.ComposeL c (onlyAsgnVars t xs es)

        LInf _           -> B.LInf (onlyInputVars t xs es)
        Prod _           -> B.Prod (onlyAsgnVars  t xs es)
        Min _            -> B.Min  (onlyAsgnVars  t xs es)
        Max _            -> B.Max  (onlyAsgnVars  t xs es)

-- the definition of Norm allows to use any variables inside argumets (both input and assignment variables)
normExpression :: Expr -> [a] -> [Norm a] -> (Norm a)
normExpression t xs es =
    let zs = (Data.List.map (\ x -> Col x) xs) ++ es in
    case t of
        PowerLN _ _      -> LN (head zs)
        ScaleNorm c _    -> NormScale c (head zs)
        ZeroSens _       -> NormZero (head zs)
        L c _            -> NormL (AtMost c) zs
        LInf _           -> NormLInf zs

---------------------------------------------------------------------------------------------
-- TODO: parsing of 'expr' and 'tableExpr' is being synchronized with B.Expr and B.TableExpr

-- keywords
allKeyWords :: [String] -- list of reserved "words"
allKeyWords = ["return","^","LN","exp","scaleNorm","zeroSens","lp","linf","prod","min","max","selectMin","selectMax","selectProd","selectL"]

-- a query expression
queryExpr :: Parser Expr
queryExpr = powerExpr
  <|> powerLNExpr
  <|> expExpr
  <|> scaleNormExpr
  <|> zeroSensExpr
  <|> lpNormExpr
  <|> linfNormExpr
  <|> prodExpr
  <|> minExpr
  <|> maxExpr

-- a norm expression
normExpr :: Parser Expr
normExpr = scaleNormExpr
  <|> zeroSensExpr
  <|> lpNormExpr
  <|> linfNormExpr
  <|> lnExpr

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

-- this one is intended for norms
lnExpr :: Parser Expr
lnExpr = do
  keyWord "LN"
  a <- varName
  return (PowerLN a 0.0)

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

-- ======================================================================= --
-----------------------------------------------------------------------------
----      The code below does not need to be updated with Banach.hs      ----
-----------------------------------------------------------------------------

------------------------------------
---- Additional data structures ----
------------------------------------

-- the format of the input file
--   "String" is the name of the database file
--   "[VarName Int]" is a list that will later be turned to a map from variable names to unique integers -- their column indices in the database
--                   we assume that the inputs listed in the input file are ordered as the columns
--   "Function" is the function on inputs that the inquirer wants to compute
data Program
  = P String [(VarName,Int)] Function
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

query :: Parser Program
query = do
  tablePath <- text
  void (delim)
  xs <- many varName
  void (delim)
  f <- function QueryParsing
  return (P tablePath (zipWith (\x y -> (x,y)) xs [0..((length xs) - 1)]) f)

norm :: Parser Program
norm = do
  xs <- many varName
  void (delim)
  f <- function NormParsing
  return (P "" (zipWith (\x y -> (x,y)) xs [0..((length xs) - 1)]) f)

asgnStmt :: ParserInstance -> Parser (VarName,Expr)
asgnStmt p = do
  a  <- varName
  void (asgn)
  b <- case p of {QueryParsing -> queryExpr; NormParsing -> normExpr}
  void (delim)
  return (a,b)

returnStmt :: ParserInstance -> Parser TableExpr
returnStmt p = do
  keyWord "return"
  a <- case p of {QueryParsing -> queryTableExpr; NormParsing -> normTableExpr}
  void (delim)
  return a

function :: ParserInstance -> Parser Function
function p = do
  as <- many (asgnStmt p)
  b  <- returnStmt p
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
readDB :: String -> IO B.Table
readDB dbFileName = do
    table <- fmap readDoubles (readInput dbFileName)
    return table

getProgramInputs :: Program -> [(VarName, Int)]
getProgramInputs (P _ inputVarList _) = inputVarList

getProgramDbFileName :: Program -> String
getProgramDbFileName (P dbFileName _ _) = dbFileName

program2Expr :: [VarName] -> (Map VarName B.Var) -> Program -> (S.Set B.Var, B.TableExpr)
program2Expr usedVarList inputMap (P _ _ (F asgnMap y))  =
    let x = extractArg y in
    let usedVars = S.fromList (Data.List.map (\x -> inputMap ! x) usedVarList) in
    let (vars,z) = matchAsgnVariable queryExpression B.ZeroSens usedVars inputMap asgnMap x in
    (vars, queryArg y z)

norm2Expr :: [VarName] -> (Map VarName B.Var) -> Program -> (S.Set B.Var, Norm B.Var)
norm2Expr usedVarList inputMap (P _ _ (F asgnMap y)) =
    let x = extractArg y in
    let usedVars = S.fromList (Data.List.map (\x -> inputMap ! x) usedVarList) in
    let (vars,z) = matchAsgnVariable normExpression NormZero usedVars inputMap asgnMap x in
    (vars, normArg y z)

processExpression :: (Show a, Ord a) => 
                         (Expr -> [a] -> [b] -> b) -> -- the function that actually rewrites the term
                         (b -> b) ->                  -- applied to terms that contain only unused variables (ZeroSens, NormZero)
                         (S.Set a) ->                 -- the set of used variables
                         (Map VarName a) ->           -- input variable map
                         (Map VarName Expr) ->        -- assigmnent variable map
                         Expr ->                      -- the expression that we rewrite
                         (S.Set a, b)
processExpression f nullify usedVars inputMap asgnMap expr =
    let varNames = extractArgs expr in
    let usedInputVarNames = Data.List.filter (\x -> member x inputMap) varNames in
    let usedAsgnVarNames  = Data.List.filter (\x -> member x asgnMap)  varNames in

    let inputVars       = Data.List.map (matchInputVariable inputMap)                           usedInputVarNames in
    let asgnInputsExprs = Data.List.map (matchAsgnVariable f nullify usedVars inputMap asgnMap) usedAsgnVarNames  in

    let (asgnInputs,asgnExprs) = Data.List.unzip asgnInputsExprs in
    (S.union (S.fromList inputVars) (Data.List.foldr S.union S.empty asgnInputs), f expr inputVars asgnExprs)

--check if the variable is a keys in a map, return the corresponding value if it is
matchInputVariable :: (Show a, Ord a) => (Map VarName a) -> VarName -> a
matchInputVariable inputMap x = (inputMap ! x)

--check if the variable is a keys in a map, apply processExpression to the value of that key
matchAsgnVariable :: (Show a, Ord a) => (Expr -> [a] -> [b] -> b) -> (b -> b) -> (S.Set a) -> (Map VarName a) -> (Map VarName Expr) -> VarName -> (S.Set a,b)
matchAsgnVariable f nullify usedVars inputMap asgnMap x =

        -- if y is an assignment variable, find its value recursively
        let expr = (asgnMap ! x) in
        let (expVars,e) = (processExpression f nullify usedVars inputMap asgnMap expr) in
        if S.null (S.intersection expVars usedVars) then (S.empty, nullify e) else (expVars,e)


-- read the DB line by line -- no speacial parsing, assume that the delimiters are whitespaces
readInput path = do
   content <- readFile path
   return content

readDoubles :: String -> [[Double]]
readDoubles s = fmap (Data.List.map read . words) (lines s)

-- putting everything together
getBanachAnalyserInput :: String -> IO (B.Table, B.TableExpr)
getBanachAnalyserInput inputFile = do
    userPr  <- parseFromFile query inputFile
    let dbFileName = getProgramDbFileName userPr
    table   <- readDB dbFileName
    ownerPr <- parseFromFile norm (dbFileName ++ ".nrm")

    -- fix integer indices for variable names
    let inputVarList = getProgramInputs userPr
    let inputMap = fromList inputVarList

    -- read owner's requirements from file
    let (ownerNormVarNames, _) = Data.List.unzip (getProgramInputs ownerPr)    
    let ownerNormVars = (Data.List.map (\x -> inputMap ! x) ownerNormVarNames)


    let (_,ownerNorm) = norm2Expr ownerNormVarNames inputMap ownerPr
    let (_,expr) = program2Expr ownerNormVarNames inputMap userPr

    putStrLn $ "Columns sensitive to the owner: " ++ show ownerNormVars
    
    let userNorm = deriveTableNorm (Data.List.map snd inputVarList) expr
    putStrLn $ "query norm = " ++ show userNorm
    putStrLn $ "owner norm = " ++ show ownerNorm

    putStrLn $ if (verifyNorm userNorm ownerNorm) then 
            "OK: the data owner's norm is at least as large as the query norm."
        else
             "WARNING: could not prove that the data owner's norm is at least as large as the query norm."
    putStrLn $ "table = " ++ show table
    putStrLn $ "expr = " ++ show expr
    return (table,expr)


