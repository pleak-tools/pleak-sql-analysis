module CreateTablesQ where

import qualified Banach as B
import PreprocessQ (readDB)
import ParserQ (parseNormFromFile)

import Data.List
import qualified Data.Set as S

createTableSql :: String -> IO String
createTableSql tableName = do
  let dbFileName = tableName ++ ".db"
  (colNames, tbl) <- readDB dbFileName
  let numRows = length tbl
  let sensTableName = tableName ++ "_sensRows"
  let normFileName = tableName ++ ".nrm"
  ((sensRows, _), _) <- parseNormFromFile normFileName
  let sensRowsSet = S.fromList sensRows
  return $
    "DROP TABLE " ++ tableName ++ ";\n" ++
    "CREATE TABLE " ++ tableName ++ " (" ++ concatMap (\ col -> col ++ " float8, ") colNames ++ "ID int8);\n" ++
    "INSERT INTO " ++ tableName ++ " VALUES\n" ++ intercalate ",\n" (zipWith (\ r i -> '(' : intercalate ", " (map show r ++ [show i]) ++ ")") tbl [0..]) ++ ";\n" ++
    "DROP TABLE " ++ sensTableName ++ ";\n" ++
    "CREATE TABLE " ++ sensTableName ++ " (ID int8, sensitive boolean);\n" ++
    "INSERT INTO " ++ sensTableName ++ " VALUES\n" ++ intercalate ",\n" (map (\ i -> '(' : show i ++ ", " ++ (if i `S.member` sensRowsSet then "true" else "false") ++ ")") [0..numRows-1]) ++ ";\n"
