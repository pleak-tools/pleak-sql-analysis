module ReaderQ where

import Data.List
import Data.Bits
import Data.Char
import qualified Data.Map as M

import ErrorMsg

-- read the DB line by line -- no speacial parsing, assume that the delimiters are whitespaces
readInput :: String -> IO String
readInput path = do
   content <- readFile path
   return content

readEither :: (Read a) => String -> Either a String
readEither s = case reads s of
              [(x, "")] -> Left x
              _ -> Right s

readErr :: (Read a) => String -> String -> a
readErr varType s = case reads s of
              [(x, "")] -> x
              _ -> error $ error_tableTypeError s varType

--readEithers :: String -> Either Bool (Either Int (Either Double String))
--readEithers s = case (reads s) :: [(Bool,String)] of
--              [(x, "")] -> Left x
--              _ -> case (reads s) :: [(Int,String)] of
--                  [(x, "")] -> Right (Left x)
--                  _ -> case (reads s) :: [(Double,String)] of
--                      [(x, "")] -> Right (Right (Left x))
--                      _ -> Right (Right (Right s))

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

-- read the database from the file as a matrix of doubles
-- read is as a single table row
readDB :: String -> IO ([String], [[Double]])
readDB dbFileName = do
    (firstLine:ls) <- fmap lines (readInput dbFileName)
    let varNames = words firstLine
    let table    = readDoubles (foldr (\x y -> x ++ "\n" ++ y) "" ls)
    return (varNames, table)

-- read the database from the file as several matrices of different data types
readDBDifferentTypes :: String -> String -> M.Map String String -> IO ([String], [[Bool]], [[Int]], [[Double]], [[String]])
readDBDifferentTypes dbFileName tableName typeMap = do
    (varNames, table) <- readDBString dbFileName
    let varTypes = map (\x -> (typeMap ! (tableName ++ "." ++ x))) varNames
    let boolCols = fmap (map (readErr "bool") .   (filterWith (== "bool") varTypes)) table :: [[Bool]]
    let intCols  = fmap (map (readErr "int") .  (filterWith (== "int") varTypes)) table :: [[Int]]
    let dblCols  = fmap (map (readErr "float") . (filterWith (== "float") varTypes)) table :: [[Double]]
    let strCols  = fmap (filterWith (== "text") varTypes) table :: [[String]]
    return (varNames, boolCols, intCols, dblCols, strCols)

--readDifferentTypes :: [String] -> String -> [[Either Bool (Either Int (Either Double String))]]
--readDifferentTypes varTypes s =
--    fmap (\xs -> zipWith readSomeType varTypes (words xs)) (lines s)

--readSomeType :: String -> String -> Either Bool (Either Int (Either Double String))
--readSomeType varType s =
--    let a1 = readEither s :: Either Bool String in
--    case a1 of
--        Left x -> if varType == "bool" then Left x else error $ error_tableTypeError x varType
--        _      -> let a2 = readEither s :: Either Int String in
--            case a2 of
--                Left  x -> if varType == "int" then Right (Left x) else error $ error_tableTypeError x varType
--                _       -> let a3 = readEither s :: Either Double String in
--                    case a3 of
--                        Left  x -> if varType == "float" then Right (Right (Left x)) else error $ error_tableTypeError x varType
--                        _       -> Right (Right (Right s))

-- read the database from the file as a matrix of strings
-- read is as a single table row
readDBString :: String -> IO ([String], [[String]])
readDBString dbFileName = do
    (firstLine:ls) <- fmap lines (readInput dbFileName)
    let varNames = words firstLine
    let table    = map words ls
    return (varNames, table)

filterWith :: (a -> Bool) -> [a] -> [b] -> [b]
filterWith f keys vals =
    let fs = filter (\(x,y) -> if f x then True else False) (zip keys vals) in
    map snd fs
