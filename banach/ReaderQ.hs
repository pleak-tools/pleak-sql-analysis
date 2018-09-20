module ReaderQ where

import Data.List
import Data.Bits
import Data.Char
import Data.List.Split
import qualified Data.Map as M
import Debug.Trace

import ErrorMsg


--
splitBySeparator :: String -> String -> [String]
splitBySeparator sep s =
   if last s == last sep then endBy sep s else splitOn sep s

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

readDoubles :: String -> String -> [[Double]]
readDoubles s separator = fmap (map readIntBoolString . (splitBySeparator separator)) (lines s)

-- read the database from the file as a matrix of doubles
-- read is as a single table row
readDB :: String -> String -> IO ([String], [[Double]])
readDB dbFileName separator = do
    (firstLine:ls) <- fmap lines (readInput dbFileName)
    let varNames = splitBySeparator separator firstLine
    let table    = readDoubles (foldr (\x y -> x ++ "\n" ++ y) "" ls) separator
    return (varNames, table)

-- read the database from the file as several matrices of different data types
readDBDifferentTypes :: String -> String -> String -> M.Map String (M.Map String String) -> IO ([String], [[Bool]], [[Int]], [[Double]], [[String]], [Int], [Int], [Int], [Int])
readDBDifferentTypes dbFileName separator tableName typeMap = do
    (varNames, table) <- readDBString dbFileName separator
    let varTypes = map (\x -> typeMap ! tableName ! x) varNames

    let filtBool   = map (\s -> map toLower (take 4 s) == "bool") varTypes
    let filtInt    = map (\s -> map toLower (take 3 s) == "int") varTypes
    let filtDouble = map (\s -> map toLower (take 5 s) == "float") varTypes
    let filtString = map (\s -> map toLower (take 4 s) == "text") varTypes

    let boolCols = fmap (map (readErr "bool") .   (filterByKey filtBool)) table :: [[Bool]]
    let intCols  = fmap (map (readErr "int") .  (filterByKey filtInt)) table :: [[Int]]
    let dblCols  = fmap (map (readErr "float") . (filterByKey filtDouble)) table :: [[Double]]
    let strCols  = fmap (filterByKey filtString) table :: [[String]]

    let indices = [0..length varNames - 1]
    let boolIndices = (filterByKey filtBool) indices
    let intIndices = (filterByKey filtInt) indices
    let dblIndices = (filterByKey filtDouble) indices
    let stringIndices = (filterByKey filtString) indices

    return (varNames, boolCols, intCols, dblCols, strCols, boolIndices, intIndices, dblIndices, stringIndices)

--readDifferentTypes :: [String] -> String -> String -> [[Either Bool (Either Int (Either Double String))]]
--readDifferentTypes varTypes s separator =
--    fmap (\xs -> zipWith readSomeType varTypes (splitBySeparator separator xs)) (lines s)

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
readDBString :: String -> String -> IO ([String], [[String]])
readDBString dbFileName separator = do
    (firstLine:ls) <- fmap lines (readInput dbFileName)
    let varNames = splitBySeparator separator firstLine
    let table    = map (splitBySeparator separator) ls
    return (varNames, table)

filterByKey :: [Bool] -> [b] -> [b]
filterByKey keys vals =
    let fs = filter (\(x,y) -> x) (zip keys vals) in
    map snd fs
