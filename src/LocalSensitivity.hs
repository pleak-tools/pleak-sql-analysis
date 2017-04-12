module LocalSensitivity (performLocalSensitivityAnalysis) where

import Control.Monad
import qualified Data.Map as Map
import qualified Data.Text as T
import Data.Map (Map)
import Data.Array.IArray
import Data.Array.Unboxed
import Data.Array.MArray
import Data.Array.IO
import Data.IORef
import Data.Char
import Text.Printf
import Database.HsSqlPpp.Catalog
import Database.HsSqlPpp.Syntax
import SelectQuery

type Table = [[Int]]
type Database = [Table]

table1 = [
  [100, 1],
  [100, 2],
  [101, 2]]

table2 = [
  [100, 1],
  [101, 2],
  [101, 3],
  [101, 5],
  [102, 4]]

table3 = [[i, 10*i] | i <- [1..100]]
table4 = [[i, 10*i+1] | i <- [3..110]]

dbTables = Map.fromList [
  ("t1", table1),
  ("t2", table2),
  ("t3", table3),
  ("t4", table4)]

sumExprBound = 1000

noise_gamma = 2.0
noise_C1 = 1 + noise_gamma
noise_C2 = 1 + noise_gamma
noise_epsilon = 1.0
noise_b2 = 0.5 -- must be in the interval (0,1)
noise_b1 = 1 - noise_b2


createDb :: [(String, Table)] -> (Database, Map String Int, Map Int String)
createDb dbt =
  let
    (tableNames, tables) = unzip dbt
  in
    (tables, Map.fromList (zip tableNames [0..]), Map.fromList (zip [0..] tableNames))

prefixSum = f 0 where
  f s [] = [s]
  f s (x : xs) = s : f (s + x) xs

nmcs :: Name -> [String]
nmcs (Name _ ncs) = map (\ (Nmc s) -> s) ncs

aggrOp :: Name -> String
aggrOp = map toLower . head . nmcs

data ScalExpr = BoolExpr BoolExpr | IntExpr IntExpr
data BoolExpr = BoolLit Bool | RelOp2 (Int -> Int -> Bool) IntExpr IntExpr | BoolOp1 (Bool -> Bool) BoolExpr | BoolOp2 (Bool -> Bool -> Bool) BoolExpr BoolExpr
data IntExpr = Ident Int | IntLit Int | ArOp1 (Int -> Int) IntExpr | ArOp2 (Int -> Int -> Int) IntExpr IntExpr

scalExprMaxAddr = f where
  f (BoolExpr e) =
    case e of
      BoolLit _ -> 0
      RelOp2 _ e1 e2 -> f (IntExpr e1) `max` f (IntExpr e2)
      BoolOp1 _ e1 -> f (BoolExpr e1)
      BoolOp2 _ e1 e2 -> f (BoolExpr e1) `max` f (BoolExpr e2)
  f (IntExpr e) =
    case e of
      Ident i -> i
      IntLit _ -> 0
      ArOp1 _ e1 -> f (IntExpr e1)
      ArOp2 _ e1 e2 -> f (IntExpr e1) `max` f (IntExpr e2)

compileScalarExpr :: (Name -> Int) -> ScalarExpr -> ScalExpr
compileScalarExpr nta = f where
  f (BooleanLit _ b) = BoolExpr (BoolLit b)
  f (NumberLit _ s) = IntExpr (IntLit (read s))
  f (Identifier _ ns) = IntExpr (Ident (nta ns))
  f (BinaryOp _ ns e1 e2) =
    let
      n = head (nmcs ns)
    in
      case n of
        "+" ->
          let
            IntExpr ie1 = f e1
            IntExpr ie2 = f e2
          in
            IntExpr $ ArOp2 (+) ie1 ie2
        "-" ->
          let
            IntExpr ie1 = f e1
            IntExpr ie2 = f e2
          in
            IntExpr $ ArOp2 (-) ie1 ie2
        "*" ->
          let
            IntExpr ie1 = f e1
            IntExpr ie2 = f e2
          in
            IntExpr $ ArOp2 (*) ie1 ie2
        "/" ->
          let
            IntExpr ie1 = f e1
            IntExpr ie2 = f e2
          in
            IntExpr $ ArOp2 div ie1 ie2
        "%" ->
          let
            IntExpr ie1 = f e1
            IntExpr ie2 = f e2
          in
            IntExpr $ ArOp2 mod ie1 ie2
        "=" ->
          let
            IntExpr ie1 = f e1
            IntExpr ie2 = f e2
          in
            BoolExpr $ RelOp2 (==) ie1 ie2
        "!=" ->
          let
            IntExpr ie1 = f e1
            IntExpr ie2 = f e2
          in
            BoolExpr $ RelOp2 (/=) ie1 ie2
        "<>" ->
          let
            IntExpr ie1 = f e1
            IntExpr ie2 = f e2
          in
            BoolExpr $ RelOp2 (/=) ie1 ie2
        "<=" ->
          let
            IntExpr ie1 = f e1
            IntExpr ie2 = f e2
          in
            BoolExpr $ RelOp2 (<=) ie1 ie2
        ">=" ->
          let
            IntExpr ie1 = f e1
            IntExpr ie2 = f e2
          in
            BoolExpr $ RelOp2 (>=) ie1 ie2
        "<" ->
          let
            IntExpr ie1 = f e1
            IntExpr ie2 = f e2
          in
            BoolExpr $ RelOp2 (<) ie1 ie2
        ">" ->
          let
            IntExpr ie1 = f e1
            IntExpr ie2 = f e2
          in
            BoolExpr $ RelOp2 (>) ie1 ie2
        "or" ->
          let
            BoolExpr be1 = f e1
            BoolExpr be2 = f e2
          in
            BoolExpr $ BoolOp2 (||) be1 be2
        "and" ->
          let
            BoolExpr be1 = f e1
            BoolExpr be2 = f e2
          in
            BoolExpr $ BoolOp2 (&&) be1 be2

-- (db, tableId) = createDb dbTables

performLocalSensitivityAnalysis :: Map CatName [(CatName, CatName)] -> QueryExpr -> IO ()
performLocalSensitivityAnalysis schema query = do
  let wheres = extractWhereExpr query
  putStrLn "performLocalSensitivityAnalysis"
  -- putStrLn "Trefs:"
  tables <- forM (selTref query) $ \ tr ->
    case tr of
      Tref _ n -> do
        let tblName = head (nmcs n)
        -- putStr "tblName = "
        -- print tblName
        return (tblName, dbTables Map.! tblName)
  let numTables = length tables
  let (db, tableId, tableName) = createDb tables
  putStrLn "Schema:"
  (tblColIdList, numColsList) <- fmap unzip $ fmap concat $ forM (Map.toList schema) $ \ (n1,ns) -> do
    let tblName = T.unpack n1
    case Map.lookup tblName tableId of
      Just tblId -> do
        let colId = (Map.fromList (zip (map (T.unpack . fst) ns) (zip (repeat tblId) [0..])) Map.!)
        putStr "n1 = "
        print n1
        putStr "ns = "
        print ns
        return [((tblName, colId), (tblId, length ns))]
      Nothing -> return []
  let tblColId = (Map.fromList tblColIdList Map.!)
  let numCols = (Map.fromList numColsList Map.!)
  let nmcsToColId [tn,cn] = tblColId tn cn
  let tblAddr = listArray (0,numTables) (prefixSum (map numCols [0..numTables-1])) :: UArray Int Int
  let nmcsToAddr ns = let (ti,ci) = nmcsToColId ns in (tblAddr ! ti) + ci
  let totalNumCols = tblAddr ! numTables
  colEq <- newArray ((0,0), (totalNumCols-1,totalNumCols-1)) False :: IO (IOUArray (Int,Int) Bool)
  putStr "tblAddr = "
  print tblAddr
  putStrLn "SelectList:"
  let
    sumExpr =
      case selSelectList query of
        SelectList _ [SelectItem _ (App _ ns [e1]) _] ->
          case aggrOp ns of
            "count" -> IntExpr (IntLit 1)
            "sum" -> compileScalarExpr (nmcsToAddr . nmcs) e1
  putStrLn "Wheres:"
  wheresForAddrArr <- newArray (0, totalNumCols-1) [] :: IO (IOArray Int [ScalExpr])
  let
    processWhere w =
      case w of
        BinaryOp _ n (Identifier _ n1) (Identifier _ n2) | nmcs n == ["="] -> do
          putStr "n = "
          print (nmcs n)
          putStr "n1 = "
          print (nmcs n1)
          print (nmcsToColId $ nmcs n1)
          let na1 = nmcsToAddr $ nmcs n1
          print na1
          putStr "n2 = "
          print (nmcs n2)
          print (nmcsToColId $ nmcs n2)
          let na2 = nmcsToAddr $ nmcs n2
          print na2
          writeArray colEq (na1,na2) True
        BinaryOp _ n w1 w2 | nmcs n == ["and"] -> do
          processWhere w1
          processWhere w2
        _ -> do
          -- print w
          let se = compileScalarExpr (nmcsToAddr . nmcs) w
          let a = scalExprMaxAddr se
          -- print a
          wheres <- readArray wheresForAddrArr a
          writeArray wheresForAddrArr a (se : wheres)
  forM_ wheres processWhere
  wheresForAddr <- freeze wheresForAddrArr :: IO (Array Int [ScalExpr])
  -- print $ map length $ elems wheresForAddr
  forM_ [0..totalNumCols-1] $ \ i -> do
    writeArray colEq (i,i) True
    forM_ [0..totalNumCols-1] $ \ j -> do
      b <- readArray colEq (j,i)
      when b $ writeArray colEq (i,j) True
  forM_ [0..totalNumCols-1] $ \ k -> do
    forM_ [0..totalNumCols-1] $ \ i -> do
      forM_ [0..totalNumCols-1] $ \ j -> do
        b1 <- readArray colEq (i,k)
        b2 <- readArray colEq (k,j)
        when (b1 && b2) $ writeArray colEq (i,j) True
  -- print =<< getElems colEq
  prevEq <- fmap (listArray (0,totalNumCols-1) :: [Maybe Int] -> Array Int (Maybe Int)) $ forM [0..totalNumCols-1] $ \ i -> do
    eqs <- fmap concat $ forM [0..i-1] $ \ j -> do
      b <- readArray colEq (i,j)
      return $ if b then [j] else []
    return $ if null eqs then Nothing else Just (maximum eqs)
  -- print prevEq

  let
    -- dtables must be in ascending order
    findDerivatives dtables = do
      putStr "Finding derivatives w.r.t. tables "
      print (map (tableName Map.!) dtables)
      let numdtables = length dtables
      let
        nlm :: Double
        nlm = if numdtables == 0 then 0 else noise_C2 / noise_b2 * (noise_C1 / noise_b1)^(numdtables - 1) / noise_epsilon^numdtables
      printf "Noise level multiplier = %0.3f\n" nlm
      row <- newArray (0, totalNumCols-1) 0 :: IO (IOUArray Int Int)
      isdtableArr <- newArray (0, totalNumCols-1) False :: IO (IOUArray Int Bool)
      forM_ dtables $ \ ti ->
        writeArray isdtableArr ti True
      isdtable <- freeze isdtableArr :: IO (UArray Int Bool)
      isdaddrArr <- newArray (0, totalNumCols-1) False :: IO (IOUArray Int Bool)
      areAllPrevEqsDaddrsArr <- newArray (0, totalNumCols-1) False :: IO (IOUArray Int Bool)
      let daddrs = concatMap (\ ti -> [tblAddr ! ti .. (tblAddr ! (ti+1))-1]) dtables
      forM_ daddrs $ \ a -> do
        writeArray isdaddrArr a True
        case prevEq ! a of
          Nothing -> writeArray areAllPrevEqsDaddrsArr a True
          Just a2 -> readArray areAllPrevEqsDaddrsArr a2 >>= writeArray areAllPrevEqsDaddrsArr a
      isdaddr <- freeze isdaddrArr :: IO (UArray Int Bool)
      areAllPrevEqsDaddrs <- freeze areAllPrevEqsDaddrsArr :: IO (UArray Int Bool)
      derivatives <- newIORef Map.empty :: IO (IORef (Map [Int] Int))
      let
        evalScalExpr :: ScalExpr -> IO (Maybe (Either Bool Int))
        evalScalExpr (BoolExpr e) =
          case e of
            BoolLit v -> return $ Just (Left v)
            RelOp2 f e1 e2 -> do
              r1 <- evalScalExpr (IntExpr e1)
              r2 <- evalScalExpr (IntExpr e2)
              return $ case (r1,r2) of
                (Just (Right v1), Just (Right v2)) -> Just (Left (f v1 v2))
                (Nothing, Just (Right v2)) -> Nothing
                (Just (Right v1), Nothing) -> Nothing
            BoolOp1 f e1 -> do
              r1 <- evalScalExpr (BoolExpr e1)
              return $ case r1 of
                Just (Left v1) -> Just (Left (f v1))
                Nothing -> Nothing
            BoolOp2 f e1 e2 -> do
              r1 <- evalScalExpr (BoolExpr e1)
              r2 <- evalScalExpr (BoolExpr e2)
              return $ case (r1,r2) of
                (Just (Left v1), Just (Left v2)) -> Just (Left (f v1 v2))
                (Nothing, Just (Left v2)) -> Nothing
                (Just (Left v1), Nothing) -> Nothing
        evalScalExpr (IntExpr e) =
          case e of
            Ident i | isdaddr ! i -> return Nothing
                    | otherwise   -> (Just . Right) <$> readArray row i
            IntLit v -> return $ Just (Right v)
            ArOp1 f e1 -> do
              r1 <- evalScalExpr (IntExpr e1)
              return $ case r1 of
                Just (Right v1) -> Just (Right (f v1))
                Nothing -> Nothing
            ArOp2 f e1 e2 -> do
              r1 <- evalScalExpr (IntExpr e1)
              r2 <- evalScalExpr (IntExpr e2)
              return $ case (r1,r2) of
                (Just (Right v1), Just (Right v2)) -> Just (Right (f v1 v2))
                (Nothing, Just (Right v2)) -> Nothing
                (Just (Right v1), Nothing) -> Nothing

        checkScalExpr :: ScalExpr -> IO Bool
        checkScalExpr e = do
          r <- evalScalExpr e
          return $ case r of
            Nothing -> True
            Just (Left True) -> True
            _ -> False

        writePrevEqs :: Int -> Int -> IO ()
        writePrevEqs a v = do
          writeArray row a v
          case prevEq ! a of
            Nothing -> return ()
            Just a2 -> writePrevEqs a2 v

        recurse _ [] = do
          v0 <- evalScalExpr sumExpr
          let
            v =
              case v0 of
                Nothing -> sumExprBound
                Just (Right v1) -> abs v1
          -- els <- getElems row
          els <- mapM (readArray row) daddrs
          -- print els
          modifyIORef derivatives $ Map.alter (\ x -> case x of Nothing -> Just v; Just n -> Just (n+v)) els
        recurse ti (currTable : ts) = do
          let ta = tblAddr ! ti
          if isdtable ! ti then do
            forM_ [ta .. (tblAddr ! (ti+1))-1] $ \ a -> do
              unless (areAllPrevEqsDaddrs ! a) $
                case prevEq ! a of
                  Just a2 -> readArray row a2 >>= writeArray row a
            recurse (ti+1) ts
          else do
            forM_ currTable $ \ tr -> do
              checksPassed <- forM (zip [0..] tr) $ \ (ci,cv) -> do
                let a = ta + ci
                writeArray row a cv
                checksPassed2 <- mapM checkScalExpr (wheresForAddr ! a)
                checkPassed3 <- case prevEq ! a of
                  Nothing -> return True
                  Just a2 ->
                    if areAllPrevEqsDaddrs ! a2 then do
                      writePrevEqs a2 cv
                      return True
                    else do
                      v2 <- readArray row a2
                      return (v2 == cv)
                return (and checksPassed2 && checkPassed3)
              when (and checksPassed) $ do
                recurse (ti+1) ts

      recurse 0 db
      ders <- readIORef derivatives
      fmap maximum $ forM (Map.assocs ders) $ \ (els,d) -> do
        let nl = nlm * fromIntegral d
        printf "%s -> %d -> noise level %0.3f\n" (show els) d nl
        return $ if numdtables == 0 then fromIntegral d else nl

    subsets [] = [[]]
    subsets (x : xs) = let ss = subsets xs in ss ++ (map (x :) ss)

  queryResult <- findDerivatives []
  noiseLevel <- maximum <$> mapM findDerivatives (tail $ subsets [0..numTables-1])
  printf "query result = %0.3f\n" queryResult
  printf "noise level to add = %0.3f\n" noiseLevel
