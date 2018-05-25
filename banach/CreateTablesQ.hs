module CreateTablesQ where

import qualified Banach as B
import ReaderQ (readDB, readDBString)
import ParserQ (parseNormFromFile)
import ErrorMsg

import Data.List
import qualified Data.Map as M
import qualified Data.Set as S

sensRows :: String -> String
sensRows tableName = tableName ++ "_sensRows"

createTableSql :: String -> IO [String]
createTableSql tableName = do
  let dbFileName = tableName ++ ".db"
  (colNames, tbl) <- readDB dbFileName
  let numRows = length tbl
  let sensTableName = sensRows tableName
  let normFileName = tableName ++ ".nrm"
  ((sensRows, _), _) <- parseNormFromFile normFileName
  let sensRowsSet = S.fromList sensRows
  return [
    "DROP TABLE IF EXISTS " ++ tableName,
    "CREATE TABLE " ++ tableName ++ " (" ++ concatMap (\ col -> col ++ " float8, ") colNames ++ "ID int8)",
    "INSERT INTO " ++ tableName ++ " VALUES\n" ++ intercalate ",\n" (zipWith (\ r i -> '(' : intercalate ", " (map show r ++ [show i]) ++ ")") tbl [0..]),
    "DROP TABLE IF EXISTS " ++ sensTableName,
    "CREATE TABLE " ++ sensTableName ++ " (ID int8, sensitive boolean)",
    "INSERT INTO " ++ sensTableName ++ " VALUES\n" ++ intercalate ",\n" (map (\ i -> '(' : show i ++ ", " ++ (if i `S.member` sensRowsSet then "true" else "false") ++ ")") [0..numRows-1])]

createTableSqlTyped :: String -> [(String, String)] -> IO [String]
createTableSqlTyped tableName types = do
  let typeMap = M.fromList types
  let dbFileName = tableName ++ ".db"
  (colNames, tbl) <- readDBString dbFileName
  let numRows = length tbl
  let sensTableName = sensRows tableName
  let normFileName = tableName ++ ".nrm"
  ((sensRows, _), _) <- parseNormFromFile normFileName
  let sensRowsSet = S.fromList sensRows
  let colTypes = map (\col -> typeMap ! (tableName ++ "." ++ col)) colNames
  return [
    "DROP TABLE IF EXISTS " ++ tableName,
    "CREATE TABLE " ++ tableName ++ " (" ++ concatMap (\ (col,t) -> col ++ " " ++ t ++", ") (zip colNames colTypes) ++ "ID int8)",
    "INSERT INTO " ++ tableName ++ " VALUES\n" ++ intercalate ",\n" (zipWith (\ r i -> '(' : intercalate ", " (zipWith stringForm r colTypes ++ [show i]) ++ ")") tbl [0..]),
    "DROP TABLE IF EXISTS " ++ sensTableName,
    "CREATE TABLE " ++ sensTableName ++ " (ID int8, sensitive boolean)",
    "INSERT INTO " ++ sensTableName ++ " VALUES\n" ++ intercalate ",\n" (map (\ i -> '(' : show i ++ ", " ++ (if i `S.member` sensRowsSet then "true" else "false") ++ ")") [0..numRows-1])]
  where
      stringForm s t = 
                       if t /= "text" then s
                       else if head s == '\'' then s
                       else if head s == '\"' then "\'" ++ tail (init s) ++ "\'"
                       else "\'" ++ s ++ "\'"
 


