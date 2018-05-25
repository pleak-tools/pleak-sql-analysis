module ReaderQ where

import Data.List
import Data.Bits
import Data.Char

-- read the DB line by line -- no speacial parsing, assume that the delimiters are whitespaces
readInput :: String -> IO String
readInput path = do
   content <- readFile path
   return content

readEither :: (Read a) => String -> Either a String
readEither s = case reads s of
              [(x, "")] -> Left x
              _ -> Right s

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

-- read the database from the file as a matrix of strings
-- read is as a single table row
readDBString :: String -> IO ([String], [[String]])
readDBString dbFileName = do
    (firstLine:ls) <- fmap lines (readInput dbFileName)
    let varNames = words firstLine
    let table    = map words ls
    return (varNames, table)

