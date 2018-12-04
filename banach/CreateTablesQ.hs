module CreateTablesQ where

import qualified Banach as B
import ReaderQ (readDB, readDBString, readDBDifferentTypes)
import ParserQ (parseNormFromFile)
import ErrorMsg

import Debug.Trace
import Data.Char
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S

sensRows :: String -> String
sensRows tableName = tableName ++ "_sensRows"

--TODO generalize to multiple row tables
createIntermediateAggrTableSql :: String -> [[String]] -> IO [String]
createIntermediateAggrTableSql tableName tbl = do
  let numRows = length tbl
  let sensTableName = sensRows tableName
  let sensRows = [0..]
  let sensRowsSet = S.fromList (take numRows sensRows)
  return [
    "INSERT INTO " ++ tableName ++ " VALUES\n" ++ intercalate ",\n" (zipWith (\ r i -> '(' : intercalate ", " (r ++ [show i]) ++ ")") tbl [0..]),
    "INSERT INTO " ++ sensTableName ++ " VALUES\n" ++ intercalate ",\n" (map (\ i -> '(' : show i ++ ", " ++ (if i `S.member` sensRowsSet then "true" else "false") ++ ")") [0..numRows-1])]

initIntermediateAggrTableSql :: String -> [String]
initIntermediateAggrTableSql tableName =
  let sensTableName = sensRows tableName in
  let colNamesTypes = [("inputTable","text"),
                   ("fx","float8"),
                   ("subf","float8"),
                   ("sdsf","float8"),
                   ("beta","float8"),
                   ("gub","float8"),
                   ("gsens","float8")] in
  [
    "DROP TABLE IF EXISTS " ++ tableName,
    "CREATE TABLE " ++ tableName ++ " (" ++ concatMap (\ (colName,typeName) -> colName ++ " " ++ typeName ++ ", ") colNamesTypes ++ "ID int8)",
    "DROP TABLE IF EXISTS " ++ sensTableName,
    "CREATE TABLE " ++ sensTableName ++ " (ID int8, sensitive boolean)"
  ]


createTableSql :: Bool -> String -> String -> String -> IO [String]
createTableSql policy dataPath separator tableName = do
  let dbFileName = dataPath ++ tableName ++ ".db"
  (colNames, tbl) <- readDB dbFileName separator
  let numRows = length tbl
  let sensTableName = sensRows tableName
  sensRows <- if policy then do return ([0..])
              else do
                  let normFileName = dataPath ++ tableName ++ ".nrm"
                  ((sR, _), _, _) <- parseNormFromFile normFileName
                  return sR

  let sensRowsSet = S.fromList (take numRows sensRows)
  return [
    "DROP TABLE IF EXISTS " ++ tableName,
    "CREATE TABLE " ++ tableName ++ " (" ++ concatMap (\ col -> col ++ " float8, ") colNames ++ "ID int8)",
    "INSERT INTO " ++ tableName ++ " VALUES\n" ++ intercalate ",\n" (zipWith (\ r i -> '(' : intercalate ", " (map show r ++ [show i]) ++ ")") tbl [0..]),
    "DROP TABLE IF EXISTS " ++ sensTableName,
    "CREATE TABLE " ++ sensTableName ++ " (ID int8, sensitive boolean)",
    "INSERT INTO " ++ sensTableName ++ " VALUES\n" ++ intercalate ",\n" (map (\ i -> '(' : show i ++ ", " ++ (if i `S.member` sensRowsSet then "true" else "false") ++ ")") [0..numRows-1])]

createTableSqlTyped :: Bool -> String -> String -> String -> [(String,[(String, String)])] -> IO [String]
createTableSqlTyped policy dataPath separator tableName types = do
  let typeMap = M.fromList $ map (\(x,ys) -> (x, M.fromList ys)) types
  let dbFileName = dataPath ++ tableName ++ ".db"
  (colNames, tbl) <- readDBString dbFileName separator

  -- TODO this piece is used only for testing, can be removed if does not work
  --(_, boolCols, intCols, dblCols, strCols, boolIndices, intIndices, dblIndices, stringIndices) <- readDBDifferentTypes dbFileName tableName typeMap
  --traceIO $ ("==== " ++ tableName ++ "====")
  --traceIO $ ("--- boolCols ---")
  --traceIO $ show boolCols ++ " " ++ show boolIndices
  --traceIO $ ("--- intCols ---")
  --traceIO $ show intCols ++ " " ++ show intIndices
  --traceIO $ ("--- dblCols ---")
  --traceIO $ show dblCols ++ " " ++ show dblIndices
  --traceIO $ ("--- strCols ---")
  --traceIO $ show strCols ++ " " ++ show stringIndices

  let numRows = length tbl
  let sensTableName = sensRows tableName
  sensRows <- if policy then do return ([0..])
              else do
                  let normFileName = dataPath ++ tableName ++ ".nrm"
                  ((sR, _), _, _) <- parseNormFromFile normFileName
                  return sR

  let sensRowsSet = S.fromList (take numRows sensRows)
  let colTypes = map (\col -> typeMap ! tableName ! col) colNames
  return [
    "DROP TABLE IF EXISTS " ++ tableName,
    "CREATE TABLE " ++ tableName ++ " (" ++ concatMap (\ (col,t) -> col ++ " " ++ t ++", ") (zip colNames colTypes) ++ "ID int8)",
    "INSERT INTO " ++ tableName ++ " VALUES\n" ++ intercalate ",\n" (zipWith (\ r i -> '(' : intercalate ", " (zipWith stringForm r colTypes ++ [show i]) ++ ")") tbl [0..]),
    "DROP TABLE IF EXISTS " ++ sensTableName,
    "CREATE TABLE " ++ sensTableName ++ " (ID int8, sensitive boolean)",
    "INSERT INTO " ++ sensTableName ++ " VALUES\n" ++ intercalate ",\n" (map (\ i -> '(' : show i ++ ", " ++ (if i `S.member` sensRowsSet then "true" else "false") ++ ")") [0..numRows-1])]
  where
      stringForm s t = 
                       if map toLower (take 4 t) /= "text" then s
                       else if head s == '\'' then s
                       else if head s == '\"' then "\'" ++ tail (init s) ++ "\'"
                       else "\'" ++ s ++ "\'"
 


