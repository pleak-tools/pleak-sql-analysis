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
import Data.Either
import Data.Maybe
import Data.List
import Debug.Trace
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
  ("t2copy", table2),
  ("t3", table3),
  ("t3copy", table3),
  ("t4", table4)]

sumExprBound = 1000

data NoiseParameters =
  NoiseParameters {
    noise_epsilon :: Double,
    noise_b2 :: Double -- must be in the interval (0,1)
  }

noise_b1 :: NoiseParameters -> Double
noise_b1 np = 1 - noise_b2 np

data NoiseDistribution =
  NoiseDistribution {
    distrBeta :: NoiseParameters -> Double, -- for smooth sensitivity
    distrSmNlm :: NoiseParameters -> Double, -- for smooth sensitivity
    distrC1 :: Double,
    distrC2 :: Double,
    distrQuantiles :: [Double] -> [Double]
  }

noise_Laplace noise_Laplace_delta =
  NoiseDistribution {
    distrBeta = \ np -> noise_b1 np * noise_epsilon np / (noise_Laplace_k - 1),
    --distrBeta = noise_epsilon / (2 * log (2 / noise_Laplace_delta)),
    --distrBeta = noise_epsilon / (2 * (log (2 / noise_Laplace_delta) - noise_epsilon)),
    --distrSmNlm = 2 / noise_epsilon,
    distrSmNlm = \ np -> 1 / (noise_b2 np * noise_epsilon np),
    distrC1 = noise_Laplace_C1,
    distrC2 = noise_Laplace_C2,
    distrQuantiles = map nqL
  }
  where
    noise_Laplace_k = - log noise_Laplace_delta
    noise_Laplace_C1 = noise_Laplace_k - 1
    noise_Laplace_C2 = 1.0
    -- quantiles of the absolute value of added noise
    nqL p = - log (1 - p)

noise_Cauchy =
  NoiseDistribution {
    distrBeta = \ np -> noise_b1 np * noise_epsilon np / (noise_Cauchy_gamma + 1),
    distrSmNlm = \ np -> (noise_Cauchy_gamma + 1) / (noise_b2 np * noise_epsilon np),
    distrC1 = noise_Cauchy_C1,
    distrC2 = noise_Cauchy_C2,
    distrQuantiles = map nqC
  }
  where
    noise_Cauchy_gamma = 2.0
    noise_Cauchy_C1 = 1 + noise_Cauchy_gamma
    noise_Cauchy_C2 = 1 + noise_Cauchy_gamma
    nqC p = tan (0.5 * pi * p)

noise_GenCauchy noise_Cauchy_gamma =
  NoiseDistribution {
    distrBeta = \ np -> noise_b1 np * noise_epsilon np / (noise_Cauchy_gamma + 1),
    distrSmNlm = \ np -> (noise_Cauchy_gamma + 1) / (noise_b2 np * noise_epsilon np),
    distrC1 = noise_Cauchy_C1,
    distrC2 = noise_Cauchy_C2,
    distrQuantiles = compute_generalized_Cauchy_distribution_quantiles noise_Cauchy_gamma
  }
  where
    noise_Cauchy_C1 = 1 + noise_Cauchy_gamma
    noise_Cauchy_C2 = 1 + noise_Cauchy_gamma

noise_distributions = [noise_GenCauchy 10.0, noise_GenCauchy 5.0, noise_GenCauchy 3.0, noise_Cauchy, noise_Laplace 1.0e-5, noise_Laplace 1.0e-10]

--noise_epsilon = 1.0
--noise_b2 = 0.5 -- must be in the interval (0,1)
--noise_b1 = 1 - noise_b2


prefixSum :: (Num a) => [a] -> [a]
prefixSum = f 0 where
  f s [] = [s]
  f s (x : xs) = s : f (s + x) xs

crossProd :: [[a]] -> [[a]]
crossProd [] = [[]]
crossProd (xs:yss) = [x : ys | x <- xs, ys <- crossProd yss]

combins :: Int -> [a] -> [[a]]
combins k xs = f (length xs) k xs where
  f _ 0 _ = [[]]
  f n k ~(x : xs)
    | n >= k    = f (n-1) k xs ++ (map (x :) $ f (n-1) (k-1) xs)
    | otherwise = []

subsets :: [a] -> [[a]]
subsets [] = [[]]
subsets (x : xs) = let ss = subsets xs in ss ++ (map (x :) ss)

permuts xs = f (length xs) xs where
  insert x 0 ys = x : ys
  insert x k (y:ys) = y : insert x (k-1) ys
  f 0 [] = [[]]
  f n (x:xs) = [insert x k p | p <- f (n-1) xs, k <- [0..n-1]]


-- A pattern is either the null pattern or a list of nonnegative integers where 0 matches any positive integer
-- e.g. [2,0,3,0] matches all lists [2,i,3,j] where i and j are any positive integers
-- The null pattern does not match anything
-- The zero pattern is a list whose all elements are 0, i.e. it matches everything
-- We define the partial order on patterns as the subset relation on the sets they match,
-- i.e. the null pattern is the smallest and the zero pattern is the largest
-- The intersection of a set of patterns P matches the lists matched by all patterns in P
-- A pattern map is mapping from a set of patterns to integers
-- A closed pattern set is a set of patterns P such that P+{null pattern} is closed under intersection and P contains the zero pattern
-- A closed pattern map is a mapping from a closed pattern set to integers
-- We merge two closed pattern maps cpm1 and cpm2 to get a new closed pattern map cpm such that
-- if p is the intersection of a pattern mapped by cpm1 and a pattern mapped by cpm2 then
-- cpm(p) = cpm1(p1) + cpm2(p2) | p <= p1 & p <= p2}
-- where p1 is the intersection of all patterns p1 mapped by cpm1 such that p <= p1
--       (i.e. the smallest pattern p1 mapped by cpm1 such that p <= p1)
-- and   p2 is the intersection of all patterns p2 mapped by cpm2 such that p <= p2
--       (i.e. the smallest pattern p2 mapped by cpm2 such that p <= p2)
-- The arguments to mergeCpms are given as sorted association lists
mergeCpms :: [([Int],[Int])] -> [([Int],[Int])] -> [([Int],[Int])]
mergeCpms [] cpm = cpm
mergeCpms cpm [] = cpm
mergeCpms [([],n1)] [([],n2)] = [([], zipWith (+) n1 n2)]
mergeCpms cpm1 cpm2 = -- trace (printf "mergeCpms %s %s" (show cpm1) (show cpm2)) $
  let
    mgb = map (\ xs -> (head (fst (head xs)), map (\ (ys,n) -> (tail ys, n)) xs)) . groupBy (\ x y -> head (fst x) == head (fst y))
    mgb1 = mgb cpm1
    mgb2 = mgb cpm2
    (c10,m1) =
      case mgb1 of
        (0,cpm):mgb -> (cpm, mgb)
        _ -> ([], mgb1)
    (c20,m2) =
      case mgb2 of
        (0,cpm):mgb -> (cpm, mgb)
        _ -> ([], mgb2)
    mapfun (ys,n) = (0:ys, n)
    cpm0 = map mapfun $ mergeCpms c10 c20
    f [] [] = []
    f [] ((x,cpm2):m2) =
      let
        mapfun (ys,n) = (x:ys, n)
      in
        map mapfun (mergeCpms c10 cpm2) ++ f [] m2
    f ((x,cpm1):m1) [] =
      let
        mapfun (ys,n) = (x:ys, n)
      in
        map mapfun (mergeCpms cpm1 c20) ++ f m1 []
    f m1f@((x1,cpm1):m1) m2f@((x2,cpm2):m2) =
      let
        x = min x1 x2
        mapfun (ys,n) = (x:ys, n)
      in
        case compare x1 x2 of
          EQ -> map mapfun (mergeCpms cpm1 cpm2) ++ f m1 m2
          LT -> map mapfun (mergeCpms cpm1 c20) ++ f m1 m2f
          GT -> map mapfun (mergeCpms c10 cpm2) ++ f m1f m2
  in
    cpm0 ++ f m1 m2

mergeManyCpms :: [[([Int],[Int])]] -> [([Int],[Int])]
mergeManyCpms [] = []
mergeManyCpms [cpm] = cpm
mergeManyCpms cpms =
  let
    (cpms1,cpms2) = splitAt (length cpms `div` 2) cpms
  in
    mergeCpms (mergeManyCpms cpms1) (mergeManyCpms cpms2)

patternIntersection :: Maybe [Int] -> Maybe [Int] -> Maybe [Int]
patternIntersection Nothing _ = Nothing
patternIntersection _ Nothing = Nothing
patternIntersection (Just p1) (Just p2) = patternIntersection' p1 p2

patternIntersection' :: [Int] -> [Int] -> Maybe [Int]
patternIntersection' [] [] = Just []
patternIntersection' (0 : xs) (y : ys) = (y :) <$> patternIntersection' xs ys
patternIntersection' (x : xs) (0 : ys) = (x :) <$> patternIntersection' xs ys
patternIntersection' (x : xs) (y : ys) | x == y    = (x :) <$> patternIntersection' xs ys
                                       | otherwise = Nothing

isPatternSubset :: [Int] -> [Int] -> Bool
isPatternSubset [] [] = True
isPatternSubset (x : xs) (0 : ys) = isPatternSubset xs ys
isPatternSubset (x : xs) (y : ys) = x == y && isPatternSubset xs ys

derMapCrossProd :: [[([Int], [Int], [Int])]] -> [([Int], [Int], [Int])]
derMapCrossProd [dm] = dm
derMapCrossProd (dm : dms) = [(e1 ++ e2, v1 ++ v2, [d1 * d2]) | let dmcp = derMapCrossProd dms, (e1,v1,[d1]) <- dm, (e2,v2,[d2]) <- dmcp]


compute_generalized_Cauchy_distribution_quantiles noise_Cauchy_gamma =
  let
    k1 = 1000
    k2 = 20
    k3 = -10
    pd x = 1 / (1 + x**noise_Cauchy_gamma)
    invk1 = (1 :: Double) / fromIntegral k1
    --samples = map ((invk1 *) . fromIntegral) [0..k1-1] ++ map ((\ i -> exp (invk1 * i)) . fromIntegral) [0..k2*k1]
    samples = 0 : map ((\ i -> exp (invk1 * i)) . fromIntegral) [k3*k1..k2*k1]
    pds = map pd samples
    ps = zipWith (*) pds $ zipWith (-) (tail samples) samples
    cps = prefixSum ps
    invtotalprob = 1 / last cps
    qlist = zip (map (invtotalprob *) cps) samples
    --forM_ (zip3 samples pds cps) $ \ (s,pd,cp) ->
    --  printf "%0.3f %0.7f %0.7f\n" s (pd*invtotalprob) (cp*invtotalprob)
    --forM_ qlist $ \ (cp,s) ->
    --  printf "%0.7f %0.3f\n" cp s
    findQuantiles = f qlist where
      f _ [] = []
      f qs@((cp,s):qs') cp0s@(cp0:cp0s')
        | cp < cp0  = f qs' cp0s
        | otherwise = s : f qs cp0s'
  in findQuantiles


nmcs :: Name -> [String]
nmcs (Name _ ncs) = map ncStr ncs

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


data JoinedRow = JoinedRow {
    getRow :: IOUArray Int Int,
    areAllPrevEqsDaddrs :: UArray Int Bool,
    evalScalExpr :: ScalExpr -> IO (Maybe (Either Bool Int)),
    checkScalExpr :: ScalExpr -> IO Bool,
    writeRowElements :: Int -> [Int] -> IO Bool,
    inferRowElement :: Int -> IO ()
  }

createJoinedRow :: Int -> Array Int (Maybe Int) -> Array Int [ScalExpr] -> [Int] -> IO JoinedRow
createJoinedRow totalNumCols prevEq wheresForAddr daddrs = do
  row <- newArray (0, totalNumCols-1) 0 :: IO (IOUArray Int Int)
  isdaddrArr <- newArray (0, totalNumCols-1) False :: IO (IOUArray Int Bool)
  areAllPrevEqsDaddrsArr <- newArray (0, totalNumCols-1) False :: IO (IOUArray Int Bool)
  forM_ daddrs $ \ a -> do
    writeArray isdaddrArr a True
    case prevEq ! a of
      Nothing -> writeArray areAllPrevEqsDaddrsArr a True
      Just a2 -> readArray areAllPrevEqsDaddrsArr a2 >>= writeArray areAllPrevEqsDaddrsArr a
  isdaddr <- freeze isdaddrArr :: IO (UArray Int Bool)
  areAllPrevEqsDaddrs <- freeze areAllPrevEqsDaddrsArr :: IO (UArray Int Bool)
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

    writeRowElement :: Int -> Int -> IO Bool
    writeRowElement a cv = do
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

    writeRowElements :: Int -> [Int] -> IO Bool
    writeRowElements a cvs = and <$> zipWithM writeRowElement [a..] cvs

    inferRowElement :: Int -> IO ()
    inferRowElement a =
      unless (areAllPrevEqsDaddrs ! a) $
        case prevEq ! a of
          Just a2 -> readArray row a2 >>= writeArray row a

  return $ JoinedRow row areAllPrevEqsDaddrs evalScalExpr checkScalExpr writeRowElements inferRowElement


showNoiseLevelList :: [Double] -> String
showNoiseLevelList [] = "[]"
showNoiseLevelList nls = take (length s - 3) s
  where s = concatMap (printf "%0.3f | " :: Double -> String) nls

showDoubleNoiseLevelList :: [Double] -> [Double] -> String
showDoubleNoiseLevelList [] [] = "[]"
showDoubleNoiseLevelList nls1 nls2 = take (length s - 3) s
  where s = concat $ zipWith (printf "%9.3f # %9.3f | " :: Double -> Double -> String) nls1 nls2


performLocalSensitivityAnalysis :: Bool -> Map CatName [(CatName, CatName)] -> QueryExpr -> IO ()
performLocalSensitivityAnalysis debug schema query = do
  putStrLn "performLocalSensitivityAnalysis"
  putStrLn "Processing the schema"
  origTableCols <- fmap Map.fromList $ forM (Map.toList schema) $ \ (n1,ns) -> do
    let tblName = T.unpack n1
    let cols = map (T.unpack . fst) ns
    return (tblName, cols)
  let np = NoiseParameters { noise_epsilon = 1, noise_b2 = 0.5 }
  --forM_ [0.1,0.2..0.9] $ \ b2 -> do
  --  _ <- performLocalSensitivityAnalysis' debug np{noise_b2 = b2} origTableCols query
  --  return ()
  _ <- performLocalSensitivityAnalysis' debug np origTableCols query
  return ()

performLocalSensitivityAnalysis' :: Bool -> NoiseParameters -> Map String [String] -> QueryExpr -> IO ([String], Table, [([(String, Int)], [([Int], [Int], [Int])])])
performLocalSensitivityAnalysis' debug np origTableCols query = do
  putStrLn "performLocalSensitivityAnalysis'"

  putStrLn "Processing FROM clause"
  (db,hasSubQueries,allSubQueryDers,tableName,newTableIds,origTables,newTableCount,numCols,tblAddr,nmcsToAddr,totalNumCols,colEq,numTables) <- do
    let tmpTableName = ('$' :)
    (tableNames, origTableNames, colNamess, db, derss) <- fmap unzip5 $ forM (selTref query) $ \ tr -> do
      case tr of
        Tref _ n -> do
          let tblName = head (nmcs n)
          printf "%s -> %s\n" tblName tblName
          return (tblName, tblName, origTableCols Map.! tblName, dbTables Map.! tblName, Nothing)
        TableAlias _ newTblName0 (Tref _ n) -> do
          let newTblName = ncStr newTblName0
          let origTblName = head (nmcs n)
          printf "%s -> %s\n" origTblName newTblName
          return (newTblName, origTblName, origTableCols Map.! origTblName, dbTables Map.! origTblName, Nothing)
        TableAlias _ newTblName0 (SubTref _ subquery) -> do
          let newTblName = ncStr newTblName0
          putStrLn "Processing subquery"
          putStrLn "==================="
          (subColNames, res, ders) <- performLocalSensitivityAnalysis' debug np origTableCols subquery
          putStrLn "============================"
          putStrLn "Finished processing subquery"
          printf "-> %s\n" newTblName
          return (newTblName, tmpTableName newTblName, subColNames, res, Just ders)
    --let subQueryDers = Map.fromList $ map (\ (x, Just y) -> (x,y)) $ filter (isJust . snd) $ zip origTableNames derss
    -- add identity subquery derivatives for those tables that are not actually results of subqueries
    let hasSubQueries = any isJust derss
    let
      allSubQueryDers = Map.fromList $ zip origTableNames $
        zipWith3
          (\ origTblName numCols ders ->
            case ders of
              Just ders -> ders
              Nothing -> let zs = replicate numCols 0 in [([(origTblName,1)],[(zs,zs,[1])])])
          origTableNames
          (map length colNamess)
          derss
    --let origTableName = (Map.fromList (zip tableNames origTableNames) Map.!)
    let numTables = length tableNames
    let tableId = (Map.fromList (zip tableNames [0..]) Map.!)
    let tableName = (Map.fromList (zip [0..] tableNames) Map.!)
    let newTableIdsMap = Map.fromList $ map (\ xs -> (fst (head xs), map (tableId . snd) xs)) $ groupBy (\ x y -> fst x == fst y) $ sort $ zip origTableNames tableNames
    let newTableIds = (newTableIdsMap Map.!)
    let origTables = Map.keys newTableIdsMap
    putStr "Tables: "
    print tableNames
    putStr "Original tables: "
    print origTables
    let newTableCount = length . newTableIds
    let colId = (Map.fromList (zip tableNames (map (\ colNames -> (Map.fromList (zip colNames [0..]) Map.!)) colNamess)) Map.!)
    let numCols = (Map.fromList (zip [0..] (map length colNamess)) Map.!)
    let nmcsToColId [tn,cn] = (tableId tn, colId tn cn)
    let tblAddr = listArray (0,numTables) (prefixSum (map numCols [0..numTables-1])) :: UArray Int Int
    let nmcsToAddr ns = let (ti,ci) = nmcsToColId ns in (tblAddr ! ti) + ci
    let totalNumCols = tblAddr ! numTables
    colEq <- newArray ((0,0), (totalNumCols-1,totalNumCols-1)) False :: IO (IOUArray (Int,Int) Bool)
    return (db,hasSubQueries,allSubQueryDers,tableName,newTableIds,origTables,newTableCount,numCols,tblAddr,nmcsToAddr,totalNumCols,colEq,numTables)

  putStrLn "Processing SELECT clause"
  let
    (selectedColNames,groupExprs,numGroupExprs,sumExprs,assembleResult,assembleDer,numAssembledVs,numSumExprs) =
      (selectedColNames,groupExprs,numGroupExprs,sumExprs,assembleResult,assembleDer,numAssembledVs,numSumExprs)
      where
        (selectedColNames, eithers) = unzip $
          case selSelectList query of
            SelectList _ sis ->
              flip map sis $ \ si ->
                (
                  case si of
                    SelectItem _ _ nc -> ncStr nc
                ,
                  case si of
                    SelectItem _ (App _ ns [e1]) _ ->
                      Left $
                        case aggrOp ns of
                          "count" -> IntExpr (IntLit 1)
                          "sum" -> cse e1
                    SelectItem _ e1 _ ->
                      Right $
                        cse e1
                )
          where
            cse = compileScalarExpr (nmcsToAddr . nmcs)
        (sumExprs0,groupExprs) =
          partitionEithers eithers
        numGroupExprs = length groupExprs
        (sumExprs,assembleResult,assembleDer,numAssembledVs) =
          if null sumExprs0
            then
              if selDistinct query == All
                then ([IntExpr (IntLit 1)], id, id, numGroupExprs)
                else ([], \ ([],vs,[]) -> ([],vs,[1]), \ (els,vs,[]) -> (els,vs,[1]), numGroupExprs)
            else
              if null groupExprs
                then (sumExprs0, \ ([],vs,d) -> ([],assembleResult0 d vs,[1]), id, numGroupExprs)
                else (sumExprs0, \ ([],vs,d) -> ([],assembleResult0 d vs,[1]), \ (els,vs,d) -> (els,assembleResult0 (map (const 0) d) vs,[2]), numExprs)
          where
            numExprs = length sumExprs0 + numGroupExprs
            -- assemble a query result row from the values of sumExprs and groupExprs
            assembleResult0 ss gs = f eithers ss gs where
              f [] [] [] = []
              f (Left _ : es) (s : ss) gs = s : f es ss gs
              f (Right _ : es) ss (g : gs) = g : f es ss gs
        numSumExprs = length sumExprs
  let aggrExprBound = fromIntegral $
                        case sumExprs of [IntExpr (IntLit n)] -> n
                                         _                    -> sumExprBound
  printf "Selected column names: %s\n" (show selectedColNames)

  putStrLn "Processing WHERE clause"
  wheresForAddr <- do
    wheresForAddrArr <- newArray (0, totalNumCols-1) [] :: IO (IOArray Int [ScalExpr])
    let
      processWhere w =
        case w of
          BinaryOp _ n (Identifier _ n1) (Identifier _ n2) | nmcs n == ["="] -> do
            let na1 = nmcsToAddr $ nmcs n1
            let na2 = nmcsToAddr $ nmcs n2
            writeArray colEq (na1,na2) True :: IO ()
          BinaryOp _ n w1 w2 | nmcs n == ["and"] -> do
            processWhere w1
            processWhere w2
          _ -> do
            let se = compileScalarExpr (nmcsToAddr . nmcs) w
            let a = scalExprMaxAddr se
            wheres <- readArray wheresForAddrArr a
            writeArray wheresForAddrArr a (se : wheres)
    let wheres = extractWhereExpr query
    forM_ wheres processWhere
    freeze wheresForAddrArr :: IO (Array Int [ScalExpr])

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

  prevEq <- fmap (listArray (0,totalNumCols-1) :: [Maybe Int] -> Array Int (Maybe Int)) $ forM [0..totalNumCols-1] $ \ i -> do
    eqs <- fmap concat $ forM [0..i-1] $ \ j -> do
      b <- readArray colEq (i,j)
      return $ if b then [j] else []
    return $ if null eqs then Nothing else Just (maximum eqs)

  let
    findSmoothSensitivityDerMap :: IO (Map (Int,Int) [([Int],Int)])
    findSmoothSensitivityDerMap = do
      -- (i,j) -> r -> the derivative of the count of table j (filtered by the where conditions) w.r.t. row r of table i
      derivatives <- newIORef Map.empty :: IO (IORef (Map (Int,Int) (Map [Int] Int)))
      forM_ (zip [0..] db) $ \ (ti,currTable) -> do
        --printf "findSmoothSensitivity: %d\n" ti
        let ta = tblAddr ! ti
        let lateAddrs = [(tblAddr ! (ti+1))..totalNumCols-1]
        let daddrs = [0..ta-1] ++ lateAddrs
        JoinedRow row areAllPrevEqsDaddrs evalScalExpr checkScalExpr writeRowElements inferRowElement <- createJoinedRow totalNumCols prevEq wheresForAddr daddrs
        forM_ currTable $ \ tr -> do
          checksPassed <- writeRowElements ta tr
          forM_ lateAddrs inferRowElement
          --printf "  %s -> %s\n" (show tr) (show checksPassed)
          when checksPassed $
            forM_ [0..numTables-1] $ \ i ->
              when (i /= ti) $ do
                tri <- mapM (readArray row) [tblAddr ! i .. (tblAddr ! (i+1)) - 1]
                --printf "    %d: %s\n" i (show tri)
                modifyIORef derivatives $
                  Map.alter
                    (\ m0 -> Just $
                      Map.alter
                        (\ n0 -> case n0 of Nothing -> Just 1; Just n -> Just (n+1))
                        tri
                        (case m0 of Nothing -> Map.empty; Just m -> m))
                    (i,ti)
      when debug $ putStrLn "findSmoothSensitivity: derivatives"
      derMaps <- readIORef derivatives
      fmap Map.fromList $ forM (Map.assocs derMaps) $ \ ((i,j),derMap) -> do
        let ders = Map.assocs derMap
        forM_ ders $ \ (r,d) ->
          when debug $ printf "  (%d,%d) -> %s -> %d\n" i j (show r) d
        return ((i,j),ders)

  smoothDerMap <- findSmoothSensitivityDerMap
  printf "distrSmNlm = %s\n" (showNoiseLevelList $ map (`distrSmNlm` np) noise_distributions)

  let
    printDerivatives :: [([Int], [Int], [Int])] -> IO ()
    printDerivatives ders = when debug $ do
      forM_ ders $ \ (els',vs,d) ->
        printf "    %s -> %s -> %s\n" (show els') (show vs) (show d) :: IO ()

    -- dtables must be in ascending order
    findDerivatives :: [Int] -> IO [([[Int]], [Int], [Int])]
    findDerivatives dtables = do
      when debug $ putStr "Finding derivatives w.r.t. tables "
      when debug $ print (map tableName dtables)
      let numdtables = length dtables
      row <- newArray (0, totalNumCols-1) 0 :: IO (IOUArray Int Int)
      isdtableArr <- newArray (0, totalNumCols-1) False :: IO (IOUArray Int Bool)
      forM_ dtables $ \ ti ->
        writeArray isdtableArr ti True
      isdtable <- freeze isdtableArr :: IO (UArray Int Bool)
      let daddrs = concatMap (\ ti -> [tblAddr ! ti .. (tblAddr ! (ti+1))-1]) dtables
      JoinedRow row areAllPrevEqsDaddrs evalScalExpr checkScalExpr writeRowElements inferRowElement <- createJoinedRow totalNumCols prevEq wheresForAddr daddrs
      derivatives <- newIORef Map.empty :: IO (IORef (Map ([Int],[Int]) [Int]))
      let
        recurse _ [] = do
          svs0 <- mapM evalScalExpr sumExprs
          let
            svs = flip map svs0 $ \ sv0 ->
              case sv0 of
                Nothing -> sumExprBound
                Just (Right v1) -> abs v1
          vs0 <- mapM evalScalExpr groupExprs
          let
            vs = flip map vs0 $ \ v0 ->
              case v0 of
                Nothing -> 0
                Just (Right v1) -> v1
          els <- mapM (readArray row) daddrs
          -- printf "  %s -> %s -> %s\n" (show els) (show vs) (show svs)
          modifyIORef derivatives $ Map.alter (\ x -> case x of Nothing -> Just svs; Just ns -> Just (zipWith (+) ns svs)) (els,vs)
        recurse ti (currTable : ts) = do
          let ta = tblAddr ! ti
          if isdtable ! ti then do
            forM_ [ta .. (tblAddr ! (ti+1))-1] inferRowElement
            recurse (ti+1) ts
          else do
            forM_ currTable $ \ tr -> do
              --checksPassed <- forM (zip [0..] tr) $ \ (ci,cv) -> do
              --  let a = ta + ci
              --  writeRowElement a cv
              checksPassed <- writeRowElements ta tr
              --when (and checksPassed) $ do
              when checksPassed $ do
                recurse (ti+1) ts

      recurse 0 db
      ders <- readIORef derivatives
      let
        ncs = map numCols dtables
        groupEls els = f els ncs where
          f [] [] = []
          f els (nc:ncs1) =
            let
              (els0,els1) = splitAt nc els
            in
              els0 : f els1 ncs1
      forM (Map.assocs ders) $ \ ((els,vs),d) -> do
        let gels = groupEls els
        --printf "%s -> %s -> %s\n" (show gels) (show vs) (show d)
        if numdtables == 1 && null vs && length d == 1
          then do
            let d1 = head d
            let currti = head dtables
            let
              satds k xs =
                if null ys || k < limit
                  then replicate (numeq - r) (x + q) ++ replicate r (x + q + 1) ++ ys
                  else satds (k - limit) (replicate numeq y ++ ys)
                where
                  x = head xs
                  numeq = length $ takeWhile (x ==) xs
                  ys = dropWhile (x ==) xs
                  y = head ys
                  limit = numeq * (y - x)
                  (q,r) = quotRem k numeq
            sds <- forM ([0..currti-1] ++ [currti+1..numTables-1]) $ \ i -> do
              when debug $ printf "  #%d:\n" i
              fmap sum $ forM (smoothDerMap Map.! (currti,i)) $ \ (r,sd) ->
                if isPatternSubset els r
                  then do
                    when debug $ printf "    %s -> %d\n" (show r) sd
                    return sd
                  else return 0
            let xs = sort sds
            let satd0 k xs = product (map (fromIntegral :: Int -> Double) (satds k xs)) * aggrExprBound
            let numMissingRows = satd0 0 xs - fromIntegral d1
            let satd k xs = satd0 k xs - numMissingRows
            let smsens0 beta k xs = satd k xs * exp (-beta * fromIntegral k)
            let
              smsens beta xs =
                let
                  isdecr k = smsens0 beta k xs > smsens0 beta (k+1) xs
                  f k = if isdecr k then k else f (2 * k)
                  g k1 k2 | k1 == k2  = k1
                          | isdecr k3 = g k1 k3
                          | otherwise = g (k3+1) k2
                    where k3 = (k1 + k2) `div` 2
                in smsens0 beta (g 0 (f 1)) xs
            let betas = map (`distrBeta` np) noise_distributions
            --printf "  beta = %s\n" (showNoiseLevelList betas)
            --printf "  1/beta = %s\n" (showNoiseLevelList (map (1/) betas))
            --forM_ [0..100] $ \ i ->
            --  printf "  %2d: %20s %10.3f %10.3f\n" i (show (satds i xs)) (satd i xs) (smsens0 beta i xs)
            let smss = map (`smsens` xs) betas
            when debug $ printf "%s -> %d # %s # %s # %s\n" (show els) d1 (show sds) (show (map ceiling smss)) (showNoiseLevelList smss)
            return (gels,vs,d++map ceiling smss)
          else
            return (gels,vs,d)

    splitUnassembledElsVs (els,d) = (els',vs,d) where
      (els',vs) = splitAt (length els - numGroupExprs) els

    splitElsVs (els,d) = (els',vs,d) where
      (els',vs) = splitAt (length els - numAssembledVs) els

    unsplitElsVs (els,vs,d) = (els ++ vs, d)

    -- dtncs contains a list of pairs of a table and the number of times to differentiate w.r.t. that table
    findDerivativesWrtOrigTables :: [(String,Int)] -> IO [([Int], [Int], [Int])]
    findDerivativesWrtOrigTables dtncs = do
      when debug $ putStr "Finding derivatives w.r.t. original tables "
      when debug $ print dtncs
      ders3 <- fmap concat $ forM (crossProd $ map (\ (tn,c) -> combins c (newTableIds tn)) dtncs) $ \ tableIdss -> do
        let tableIds = concat tableIdss
        let sti = sort tableIds
        ders <- findDerivatives sti
        ders2 <- fmap concat $ forM ders $ \ (gels,vs,d) -> do
          let tels = (Map.fromList (zip sti gels) Map.!)
          let oels = map (map tels) tableIdss
          let poelss = crossProd (map permuts oels)
          forM poelss $ \ poels -> do
            return (concat (concat poels) ++ vs, d)
        return ders2
      let ders4 = map splitUnassembledElsVs ders3
      --when debug $ putStrLn "ders4:"
      --printDerivatives ders4
      let ders5 = map (if null dtncs then assembleResult else assembleDer) ders4
      --when debug $ putStrLn "ders5:"
      --printDerivatives ders5
      return ders5

    findAllDerivativesWrtOrigTables :: IO [([(String,Int)], [([Int], [Int], [Int])])]
    findAllDerivativesWrtOrigTables =
      let
        f dtncs [] = (\ x -> [(dtncs,x)]) <$> findDerivativesWrtOrigTables dtncs
        f dtncs ((tn,ntc) : tncs) =
          fmap concat $ forM [0..ntc] $ \ i ->
            f (if i == 0 then dtncs else (tn,i) : dtncs) tncs
      in
        f [] (zip origTables (map newTableCount origTables))

  -- print $ mergeManyCpms [[([0,1],1),([0,2],2)], [([1,0],10),([2,0],20)]]
  (_,queryResult0) : derivatives <- findAllDerivativesWrtOrigTables
  let
    queryResult = concatMap getResult queryResult0
      where getResult ([],vs,[d]) = replicate d vs
  let canComputeNoiseLevel = numGroupExprs == 0 && numSumExprs == 1
  let
    combineSubQueryDers :: IO [([(String,Int)], [([Int], [Int], [Int])])]
    combineSubQueryDers =
      fmap concat $ forM derivatives $ \ (dtncs,ders) -> do
      when debug $ putStr "Derivatives w.r.t. original tables "
      when debug $ print dtncs
      let
        printDerivatives' tn dtncs ders = when debug $ do
          printf "  Derivatives of table %s w.r.t. tables %s\n" tn (show dtncs) :: IO ()
          printDerivatives ders
        findAllDers = f [] where
          f rs [] = do
              when debug $ print newdtnc
              forM_ rs' $ \ (tn,tncs',ders) -> printDerivatives' tn tncs' ders
              let cpDers = derMapCrossProd derss
              when debug $ putStrLn "  Cross product:"
              printDerivatives cpDers
              when debug $ printf "  Derivatives of result table w.r.t. tables %s\n" (show dtncs)
              printDerivatives ders
              let ders2 = [(e1,v2,map (d1 *) d2s) | (e1,v1,[d1]) <- cpDers, (e2,v2,d2s) <- ders, let v1e2 = patternIntersection' v1 e2, isJust v1e2]
              when debug $ printf "  Derivatives of result table w.r.t. tables %s\n" (show newdtnc)
              printDerivatives ders2
              return [(newdtnc,ders2)]
            where
              rs' = reverse rs
              (tns,newdtncs0,derss) = unzip3 rs'
              newdtnc = concat newdtncs0
          f rs (tnc@(tn,ntc) : tncs) =
            if ntc >= 1
              then
                fmap concat $ forM (allSubQueryDers Map.! tn) $ \ (tncs',ders) -> do
                  f ((tn,tncs',ders) : rs) tncs
              else
                f rs tncs
      findAllDers dtncs
  ders3 <- if hasSubQueries then combineSubQueryDers else return derivatives
  nlss <- fmap transpose $ forM ders3 $ \ (dtncs,ders) -> do
    putStr "Combined derivatives w.r.t. original tables "
    print dtncs
    let ders4 = map splitElsVs $ mergeManyCpms (map ((:[]) . unsplitElsVs) ders)
    let numdtables = sum (map snd dtncs)
    let
      nlm :: Double -> Double -> Double
      nlm noise_C1 noise_C2 = if numdtables == 0 then 0 else noise_C2 / noise_b2 np * (noise_C1 / noise_b1 np) ^ (numdtables - 1) / noise_epsilon np ^ numdtables

      distr_nlm :: NoiseDistribution -> Double
      distr_nlm d = nlm (distrC1 d) (distrC2 d)
    let distr_nlms = map distr_nlm noise_distributions
    let distr_smnlms = map (`distrSmNlm` np) noise_distributions
    let canComputeSmoothNoiseLevel = canComputeNoiseLevel && numdtables == 1
    when canComputeNoiseLevel $ printf "Noise level multiplier = %s\n" (showNoiseLevelList distr_nlms)
    when canComputeSmoothNoiseLevel $ printf "Smooth noise level multiplier = %s\n" (showNoiseLevelList distr_smnlms)
    maxd:maxsmss <- fmap (map maximum . transpose) $ forM ders4 $ \ (els',vs,d) -> do
      let d1 = if null d then 1 else head d
      --if canComputeNoiseLevel
      --  then printf "%s -> %s -> %s -> noise level %0.3f | %0.3f\n" (show els') (show vs) (show d) nlC nlL
      --  else printf "%s -> %s -> %s\n" (show els') (show vs) (show d)
      printf "%s -> %s -> %s\n" (show els') (show vs) (show d)
      --return nl
      if canComputeNoiseLevel && length d >= 1
        then return (map fromIntegral d)
        else return [fromIntegral d1]
    let nls = map (* maxd) distr_nlms
    let smnls = zipWith (*) maxsmss distr_smnlms
    when canComputeNoiseLevel $ printf "-> noise level %s\n" (showNoiseLevelList nls)
    when canComputeSmoothNoiseLevel $ printf "-> smooth noise level %s\n" (showNoiseLevelList smnls)
    --when canComputeNoiseLevel $ printf "-> noise level %0.3f | %0.3f\n" nlC nlL
    return $ nls ++ if null smnls then replicate (length nls) 0 else smnls
  let noiseLevels = map maximum nlss
  let (nls1,nls2) = splitAt (length noise_distributions) noiseLevels
  if canComputeNoiseLevel
    then do
      printf "query result = %0.3f\n" (fromIntegral (head (head queryResult)) :: Double)
      printf "noise level to add = %s\n" (showDoubleNoiseLevelList nls1 nls2)
      -- quantiles of the absolute value of added noise
      let ps = 0 : 0.001 : 0.01 : 0.1 : 0.2 : 0.3 : 0.4 : map (\ i -> 1 - (2 :: Double)**(- 1.0 * i)) [1..20]
      let nqss = transpose $ map (flip distrQuantiles ps) noise_distributions
      forM_ (zip ps nqss) $ \ (p, nqs) -> do
        let qs1 = zipWith (*) nls1 nqs
        let qs2 = zipWith (*) nls2 nqs
        --printf "%9.5f%% quantile: %0.3f %0.3f | %0.3f | ratio = %0.3f\n" (100 * p) (noiseLevelC * nqGC) qC qL (qC / qL)
        printf "%9.5f%% quantile: %s\n" (100 * p) (showDoubleNoiseLevelList qs1 qs2)
    else do
      putStrLn "query result:"
      mapM_ print queryResult
  return (selectedColNames, queryResult, derivatives)
