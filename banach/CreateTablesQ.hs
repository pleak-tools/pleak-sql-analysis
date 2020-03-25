module CreateTablesQ where

import qualified Banach as B
import AexprQ
import GroupQ
import ReaderQ (readDB, readDBString, readDBDifferentTypes)
import ParserQ (parseNormFromFile)
import ErrorMsg
import ProgramOptions

import Debug.Trace
import Data.Char
import Data.List
import Data.List.Split
import qualified Data.Map as M
import qualified Data.Set as S

sensRows :: String -> String
sensRows tableName = tableName ++ "_sensRows"

insertUniqueIntoIntermediateAggrTableSql :: String -> [[String]] -> [String]
insertUniqueIntoIntermediateAggrTableSql tableName tbl =
  let numRows = length tbl in
  let sensTableName = sensRows tableName in
  let sensRows = [0..] in
  let sensRowsSet = S.fromList (take numRows sensRows) in

  (map (insertUniqueOneRow tableName) tbl) ++ ["INSERT INTO " ++ sensTableName ++ " SELECT " ++ intercalate ", " (map (\ i -> show i ++ ", " ++ (if i `S.member` sensRowsSet then "true" else "false")) [0..numRows-1]) ++ " WHERE NOT EXISTS (SELECT 1 FROM " ++ sensTableName ++ " WHERE id = 0)"]

insertUniqueOneRow :: String -> [String] -> String
insertUniqueOneRow tableName tbl =
  let values = intercalate ", " (zipWith (\ r i -> intercalate ", " (r ++ [show i])) [tbl] [0..]) in
  "INSERT INTO " ++ tableName ++ " SELECT " ++ values ++ " EXCEPT SELECT * FROM " ++ tableName

insertIntoIntermediateAggrTableSql :: String -> [[String]] -> [String]
insertIntoIntermediateAggrTableSql tableName tbl =
  let numRows = length tbl in
  let sensTableName = sensRows tableName in
  let sensRows = [0..] in
  let sensRowsSet = S.fromList (take numRows sensRows) in
  [
    "INSERT INTO " ++ tableName ++ " VALUES\n" ++ intercalate ",\n" (zipWith (\ r i -> '(' : intercalate ", " (r ++ [show i]) ++ ")") tbl [0..]),
    "INSERT INTO " ++ sensTableName ++ " SELECT " ++ intercalate ", " (map (\ i -> show i ++ ", " ++ (if i `S.member` sensRowsSet then "true" else "false")) [0..numRows-1]) ++ " WHERE NOT EXISTS (SELECT 1 FROM " ++ sensTableName ++ " WHERE id = 0)"]

insertUniqueIntoIntermediateAggrTableSensSql :: String -> String -> Int -> [String] -> [String]
insertUniqueIntoIntermediateAggrTableSensSql tableName uniqueColName uniqueColIndex tbl =
  ["INSERT INTO " ++ tableName ++ " SELECT " ++ (intercalate ", " tbl) ++ " WHERE NOT EXISTS (SELECT 1 FROM " ++ tableName ++ " WHERE " ++ uniqueColName ++ " = " ++ tbl !! uniqueColIndex ++ ")"]

insertIntoIntermediateAggrTableSensSql :: String -> [[String]] -> [String]
insertIntoIntermediateAggrTableSensSql tableName tbl =
  ["INSERT INTO " ++ tableName ++ " VALUES\n" ++ intercalate ",\n" (map (\ r -> '(' : intercalate ", " r ++ ")") tbl)]

initIntermediateAggrTableSql :: M.Map String String -> String -> GroupData -> [String]
initIntermediateAggrTableSql typeMap queryName group =
  let tableName = queryNameToTableName queryName in
  let aggrCol = queryNameToVarName queryName in
  let groupCol = getGroupColName group in
  let groupVar = getGroupVarName group in

  let sensTableName = sensRows tableName in
  let colNamesTypes = [(aggrCol, "float8"), ("tableName", "text")] ++ (zipWith (\x y -> (x,   typeMap ! y)) groupCol groupVar) in
  [
    "DROP TABLE IF EXISTS " ++ tableName,
    "CREATE TABLE " ++ tableName ++ " (" ++ concatMap (\ (aggrCol,typeName) -> aggrCol ++ " " ++ typeName ++ ", ") colNamesTypes ++ "ID int8)",
    "DROP TABLE IF EXISTS " ++ sensTableName,
    "CREATE TABLE " ++ sensTableName ++ " (ID int8, sensitive boolean)",
    "DROP TABLE IF EXISTS " ++ "_sens_" ++ tableName,
    "CREATE TABLE _sens_" ++ tableName ++ " (" ++ (let (aggrCol,typeName) = head colNamesTypes in aggrCol ++ "_subf " ++ typeName ++ ", " ++ aggrCol ++ "_sdsf " ++ typeName)
                                               ++ concatMap (\ (aggrCol,typeName) -> ", " ++ aggrCol ++ " " ++ typeName) (tail colNamesTypes) ++ ")"
  ]


--createTableSql :: Bool -> String -> String -> String -> IO [String]
--createTableSql policy dataPath separator tableName = do
--  let dbFileName = dataPath ++ tableName ++ ".db"
--  (colNames, tbl) <- readDB dbFileName separator
--  let numRows = length tbl
-- let sensTableName = sensRows tableName
--  sensRows <- if policy then do return ([0..])
--              else do
--                  let normFileName = dataPath ++ tableName ++ ".nrm"
--                  ((sR, _), _, _) <- parseNormFromFile normFileName
--                  return sR

--  let sensRowsSet = S.fromList (take numRows sensRows)
--  return [
--    "DROP TABLE IF EXISTS " ++ tableName,
--    "CREATE TABLE " ++ tableName ++ " (" ++ concatMap (\ col -> col ++ " float8, ") colNames ++ "ID int8)",
--    "INSERT INTO " ++ tableName ++ " VALUES\n" ++ intercalate ",\n" (zipWith (\ r i -> '(' : intercalate ", " (map show r ++ [show i]) ++ ")") tbl [0..]),
--    "DROP TABLE IF EXISTS " ++ sensTableName,
--    "CREATE TABLE " ++ sensTableName ++ " (ID int8, sensitive boolean)",
--    "INSERT INTO " ++ sensTableName ++ " VALUES\n" ++ intercalate ",\n" (map (\ i -> '(' : show i ++ ", " ++ (if i `S.member` sensRowsSet then "true" else "false") ++ ")") [0..numRows-1])]

createTableSqlTyped :: ProgramOptions -> String -> String -> String -> [Int] -> [(String,[(String, String)])] -> IO [String]
createTableSqlTyped args dataPath separator tableName sRows types = do

    let policy = policyAnalysis args
    let datestyle = psqlDateStyle args

    let dbFileName = dataPath ++ tableName ++ ".db"

    let typeMap = M.fromList $ map (\(x,ys) -> (x, M.fromList ys)) types
    (colNames, tbl) <- readDBString dbFileName separator

    let numRows = length tbl
    let sensTableName = sensRows tableName

    -- TODO I thought that sRows will automatically be [0..] for policy, but something is wrong there
    let sR = if policy then [0..] else sRows
    --sR <- if policy then do return ([0..])
    --      else do
    --              let normFileName = dataPath ++ tableName ++ ".nrm"
    --              ((sR', _), _, _) <- parseNormFromFile (typeMap ! tableName) normFileName
    --              return sR'

    let sensRowsSet = S.fromList (take numRows sR)
    let colTypes = map (\col -> let tm = typeMap ! tableName in
                                if M.member col tm then tm ! col else error $ error_schema_bad_var tableName col (M.keys tm)) colNames
    let tblChunks      = chunksOf 100 tbl
    let rowIndexChunks = chunksOf 100 [0..numRows-1]

    let insertIntoMain  = if (numRows > 0) then
                              zipWith (\xs ys -> "INSERT INTO " ++ tableName ++ " VALUES\n" ++ intercalate ",\n" (zipWith (\ r i -> '(' : intercalate ", " (zipWith stringForm r colTypes ++ [show i]) ++ [')']) xs ys)) tblChunks rowIndexChunks
                          else [""]

    let insertIntoSRows = if (numRows > 0) then
                              map (\xs -> "INSERT INTO " ++ sensTableName ++ " VALUES\n" ++ intercalate ",\n" (map (\ i -> '(' : show i ++ ", " ++ (if i `S.member` sensRowsSet then "true" else "false") ++ [')']) xs)) rowIndexChunks
                          else [""]

    return ([
          "SET datestyle TO " ++ datestyle,
          "DROP TABLE IF EXISTS " ++ tableName,
          "CREATE TABLE " ++ tableName ++ " (" ++ concatMap (\ (col,t) -> col ++ " " ++ t ++", ") (zip colNames colTypes) ++ "ID int8)"
      ] ++ insertIntoMain ++ [
          "DROP TABLE IF EXISTS " ++ sensTableName,
          "CREATE TABLE " ++ sensTableName ++ " (ID int8, sensitive boolean)"
      ] ++ insertIntoSRows)
    where
        stringForm s t =
                       if length s == 0 then "NULL"
                       else if map toLower (take 3 t) /= "int" && map toLower (take 5 t) /= "float" && map toLower (take 6 t) /= "bigint" then
                           if head s == '\'' then s
                           else if head s == '\"' then "\'" ++ tail (init s) ++ "\'"
                           else "\'" ++ s ++ "\'"
                       else s
 


