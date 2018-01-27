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
data Expr = Power VarName Double          -- x^r with norm | |, or E^r with norm N
          | PowerLN VarName Double        -- x^r with logarithmic norm: ||x|| = |ln x|, addition in Banach space is multiplication of real numbers
          | Exp Double VarName            -- e^(r*x) with norm | |
          | Sigmoid Double Double VarName -- s(a,c,x) = e^(a*(x-c))/(e^(a*(x-c)) + 1)
          | ScaleNorm Double VarName      -- E with norm a * N
          | ZeroSens VarName              -- E with sensitivity forced to zero (the same as ScaleNorm with a -> infinity)
          | L Double [VarName]            -- ||(x1,...,xn)||_p with l_q-norm where q = p/(p-1)
          | ComposeL Double [VarName]     -- ||(E1,...,En)||_p with norm ||(N1,...,Nn)||_p
          | LInf [VarName]                -- same with p = infinity, q = 1
          | Prod [VarName]                -- E1*...*En with norm ||(N1,...,Nn)||_1 or N, where N is the common norm of all Ei
          | Min [VarName]                 -- min{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
          | Max [VarName]                 -- max{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
  deriving Show

-- expressions of type TableExpr use values from the whole table
-- the argument becomes a list when a query gets linked to a database
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

queryArg :: TableExpr -> [B.Expr] -> B.TableExpr
queryArg t ys =
    case t of
        SelectProd _ -> B.SelectProd ys
        SelectMin _  -> B.SelectMin ys
        SelectMax _  -> B.SelectMax ys
        SelectL c _  -> B.SelectL c ys

normArg :: TableExpr -> Norm a -> Norm a
normArg t y =
    case t of
        SelectProd _ -> NormL Any [y]
        SelectMin _  -> NormL Any [y]
        SelectMax _  -> NormL Any [y]
        SelectL c _  -> NormL (Exactly c) [y]

-- Expr constructor variable arguments can be Var, Expr
-- we put all of them into one list and later check whether a variable is an input or an assignment variable
extractArgs :: Expr -> [VarName]
extractArgs t =
    case t of
        Power x _        -> [x]
        PowerLN x _      -> [x]
        Exp _ x          -> [x]
        Sigmoid _ _ x    -> [x]
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
-- arg1: the term
-- arg2: used input variables
-- arg3: used assignment variables
-- arg4: the list of input vars in turn used by asgn variables -- needed e.g to decide whether Prod becomes B.Prod or B.Prod2
queryExpression :: Expr -> [B.Var] -> [B.Expr] -> [S.Set B.Var] -> B.Expr
queryExpression t xs es vss =
    case t of
        Power _ c        -> if xs /= [] then
                                B.Power (headInputVar t xs) c
                            else
                                B.ComposePower (headAsgnVar t es) c
        PowerLN _ c      -> B.PowerLN (headInputVar t xs) c
        Exp c _          -> B.Exp c (headInputVar t xs)
        Sigmoid a c x    -> B.Sigmoid a c (headInputVar t xs)
        ScaleNorm c _    -> B.ScaleNorm c (headAsgnVar t es)
        ZeroSens _       -> B.ZeroSens (headAsgnVar t es)
        L c _            -> if xs /= [] then
                                B.L c (onlyInputVars t xs es)
                            else
                                B.ComposeL c (onlyAsgnVars t xs es)

        LInf _           -> B.LInf (onlyInputVars t xs es)
        Prod _           -> if (pairwiseDisjoint vss) then -- checks if the variables of different args are pairwise disjoint
                                B.Prod (onlyAsgnVars  t xs es)
                            else
                                B.Prod2 (onlyAsgnVars  t xs es)
        Min _            -> B.Min  (onlyAsgnVars  t xs es)
        Max _            -> B.Max  (onlyAsgnVars  t xs es)

-- the definition of Norm allows to use any variables inside argumets (both input and assignment variables)
normExpression :: Expr -> [a] -> [Norm a] -> [S.Set a] -> (Norm a)
normExpression t xs es _ =
    let zs = (Data.List.map (\ x -> Col x) xs) ++ es in
    case t of
        PowerLN _ _      -> NormLN (head zs)
        ScaleNorm c _    -> NormScale c (head zs)
        ZeroSens _       -> NormZero (head zs)
        L c _            -> NormL (Exactly c) zs
        LInf _           -> NormL Any zs

pairwiseDisjoint :: [S.Set B.Var] -> Bool
pairwiseDisjoint [] = True
pairwiseDisjoint (vs:vss) =
    let n = length $ Data.List.filter (\vs' -> not (S.null (S.intersection vs vs'))) vss in
    if (n == 0) then pairwiseDisjoint vss else False

---------------------------------------------------------------------------------------------
-- TODO: parsing of 'expr' and 'tableExpr' is being synchronized with B.Expr and B.TableExpr

-- keywords
allKeyWords :: [String] -- list of reserved "words"
allKeyWords = ["return","^","LN","exp","scaleNorm","zeroSens","lp","linf","prod","min","max","sigmoid","selectMin","selectMax","selectProd","selectL"]

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
  <|> sigmoidExpr

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

sigmoidExpr :: Parser Expr
sigmoidExpr = do
  keyWord "sigmoid"
  a <- float
  c <- float
  x <- varName
  return (Sigmoid a c x)

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

-- the first row in the norm file is the list of sensitive rows
norm :: Parser ([Int],Program)
norm = do
  is <- many integer
  xs <- many varName
  void (delim)
  f <- function NormParsing
  return (is, P "" (zipWith (\x y -> (x,y)) xs [0..((length xs) - 1)]) f)

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

-- we need to read string identifiers and afterwards map them to integers
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

program2Expr :: Int -> [VarName] -> [Int] -> (Map VarName B.Var) -> Program -> (S.Set B.Var, B.TableExpr)
program2Expr numOfRows sensitiveVars sensitiveRows inputMap (P _ _ (F asgnMap y))  =
    let x = extractArg y in
    let sensitiveCols = S.fromList (Data.List.map (\x -> inputMap ! x) sensitiveVars) in
    let (vars,z) = matchAsgnVariable queryExpression B.ZeroSens sensitiveCols inputMap asgnMap x in
    -- the parameter 1 denotes that the indexation starts from 1, not from 0
    let zs = mapNotAtIndices (\x -> B.ZeroSens x) sensitiveRows (replicate numOfRows z) 1 in
    (vars, queryArg y zs)

norm2Expr :: Int -> [VarName] -> [Int] -> (Map VarName B.Var) -> Program -> (S.Set B.Var, Norm B.Var)
norm2Expr numOfRows sensitiveVars sensitiveRows inputMap (P _ _ (F asgnMap y)) =
    let x = extractArg y in
    let sensitiveCols = S.fromList (Data.List.map (\x -> inputMap ! x) sensitiveVars) in
    let (vars,z) = matchAsgnVariable normExpression NormZero sensitiveCols inputMap asgnMap x in
    (vars, normArg y z)

processExpression :: (Show a, Ord a) => 
                     (Expr -> [a] -> [b] -> [S.Set a] -> b) -> -- the function that actually rewrites the term
                     (b -> b) ->                               -- applied to terms that contain only unused variables (ZeroSens, NormZero)
                     (S.Set a) ->                              -- the set of used variables
                     (Map VarName a) ->                        -- input variable map
                     (Map VarName Expr) ->                     -- assigmnent variable map
                     Expr ->                                   -- the expression that we rewrite
                     (S.Set a, b)
processExpression f nullify usedVars inputMap asgnMap expr =
    let varNames = extractArgs expr in
    let usedInputVarNames = Data.List.filter (\x -> member x inputMap) varNames in
    let usedAsgnVarNames  = Data.List.filter (\x -> member x asgnMap)  varNames in

    let inputVars       = Data.List.map (matchInputVariable inputMap)                           usedInputVarNames in
    let asgnInputsExprs = Data.List.map (matchAsgnVariable f nullify usedVars inputMap asgnMap) usedAsgnVarNames  in

    let (asgnInputs,asgnExprs) = Data.List.unzip asgnInputsExprs in
    (S.union (S.fromList inputVars) (Data.List.foldr S.union S.empty asgnInputs), f expr inputVars asgnExprs asgnInputs)

--check if the variable is a keys in a map, return the corresponding value if it is
matchInputVariable :: (Show a, Ord a) => (Map VarName a) -> VarName -> a
matchInputVariable inputMap x = (inputMap ! x)

--check if the variable is a keys in a map, apply processExpression to the value of that key
matchAsgnVariable :: (Show a, Ord a) => (Expr -> [a] -> [b] -> [S.Set a] -> b) -> (b -> b) -> (S.Set a) -> (Map VarName a) -> (Map VarName Expr) -> VarName -> (S.Set a,b)
matchAsgnVariable f nullify usedVars inputMap asgnMap x =

        -- if y is an assignment variable, find its value recursively
        let expr = (asgnMap ! x) in
        let (expVars,e) = (processExpression f nullify usedVars inputMap asgnMap expr) in
        if S.null (S.intersection expVars usedVars) then (S.empty, nullify e) else (expVars,e)

-- transforms elements that are not on certain index positions, assumes that the indices are sorted
mapNotAtIndices :: (a -> a) -> [Int] -> [a] -> Int -> [a]
mapNotAtIndices f [] xs _ = Data.List.map f xs
mapNotAtIndices _ _ [] _ = error ("index out of bounds")
mapNotAtIndices f is'@(i:is) (x:xs) k =
    if (i == k) then x:(mapNotAtIndices f is xs (k+1))
    else (f x):(mapNotAtIndices f is' xs (k+1))

-- read the DB line by line -- no speacial parsing, assume that the delimiters are whitespaces
readInput path = do
   content <- readFile path
   return content

readDoubles :: String -> [[Double]]
readDoubles s = fmap (Data.List.map read . words) (lines s)

-- putting everything together
getBanachAnalyserInput :: String -> IO (B.Table, B.TableExpr)
getBanachAnalyserInput inputFile = do
    queryPr  <- parseFromFile query inputFile
    let dbFileName = getProgramDbFileName queryPr
    table   <- readDB dbFileName
    let numOfRows = length table
    (dbSensitiveRows,dbPr) <- parseFromFile norm (dbFileName ++ ".nrm")
    let maxIndex = Data.List.foldr max 0 dbSensitiveRows
    putStrLn $ if (maxIndex > numOfRows) then error ("The database has only " ++ show numOfRows ++ " rows, but row " ++ show maxIndex ++ " is described as sensitive.")
               else "Sensitive rows of the database: " ++ show dbSensitiveRows

    -- fix integer indices for variable names
    let inputVarList = getProgramInputs queryPr
    let inputMap = fromList inputVarList

    -- read db's requirements from file
    let (dbSensitiveVarNames, _) = Data.List.unzip (getProgramInputs dbPr)    
    let dbSensitiveVars = (Data.List.map (\x -> inputMap ! x) dbSensitiveVarNames)

    let (_,dbNorm) = norm2Expr numOfRows dbSensitiveVarNames dbSensitiveRows inputMap dbPr
    let (_,expr) = program2Expr numOfRows dbSensitiveVarNames dbSensitiveRows inputMap queryPr

    putStrLn $ "Sensitive columns of the database: " ++ show dbSensitiveVars
    
    let queryNorm = deriveTableNorm (Data.List.map snd inputVarList) expr
    putStrLn $ "query norm = " ++ show queryNorm
    putStrLn $ "database norm = " ++ show dbNorm

    let newNorm = normalizeAndVerify queryNorm dbNorm
    let adjustedExpr = case newNorm of
            Just norm -> updateTableExpr expr norm
            Nothing -> expr

    let newQueryNorm = deriveTableNorm (Data.List.map snd inputVarList) adjustedExpr
    putStrLn $ "adjusted query norm = " ++ show newQueryNorm
    putStrLn $ "variable norm scaling: " ++ case newNorm of {Nothing -> "???\n"; Just norm -> show (extractScalings norm) ++ "\n"}

    putStrLn $ case newNorm of
            Just _  -> "OK: the database norm is at least as large as the query norm."
            Nothing -> "WARNING: could not prove that the database norm is at least as large as the query norm."

    putStrLn $ "----------------"
    putStrLn $ "table = " ++ show table
    putStrLn $ "initial expr = " ++ show expr
    putStrLn $ "adjusted expr = " ++ show adjustedExpr
    putStrLn $ "----------------"
    --putStrLn $ show (mapNotAtIndices (+ 11) [2,4,5] [100,200,300,400,500,600,700] 1)
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


