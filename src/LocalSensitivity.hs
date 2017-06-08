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
  ("t4", table4)]

sumExprBound = 1000

data NoiseDistribution = NoiseDistribution { distrC1 :: Double, distrC2 :: Double, distrQuantiles :: [Double] -> [Double] }

noise_Laplace noise_Laplace_delta =
  NoiseDistribution {
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
    distrC1 = noise_Cauchy_C1,
    distrC2 = noise_Cauchy_C2,
    distrQuantiles = compute_generalized_Cauchy_distribution_quantiles noise_Cauchy_gamma
  }
  where
    noise_Cauchy_C1 = 1 + noise_Cauchy_gamma
    noise_Cauchy_C2 = 1 + noise_Cauchy_gamma

noise_distributions = [noise_GenCauchy 10.0, noise_GenCauchy 5.0, noise_GenCauchy 3.0, noise_Cauchy, noise_Laplace 1.0e-5, noise_Laplace 1.0e-10]

{-
noise_Cauchy_gamma = 5.0
noise_Cauchy_C1 = 1 + noise_Cauchy_gamma
noise_Cauchy_C2 = 1 + noise_Cauchy_gamma

noise_Laplace_delta = 1.0e-5
noise_Laplace_k = - log noise_Laplace_delta
noise_Laplace_C1 = noise_Laplace_k - 1
noise_Laplace_C2 = 1.0
-}

noise_epsilon = 1.0
noise_b2 = 0.5 -- must be in the interval (0,1)
noise_b1 = 1 - noise_b2


prefixSum :: (Num a) => [a] -> [a]
prefixSum = f 0 where
  f s [] = [s]
  f s (x : xs) = s : f (s + x) xs

compute_generalized_Cauchy_distribution_quantiles noise_Cauchy_gamma =
  let
    k1 = 1000
    k2 = 20
    pd x = 1 / (1 + x**noise_Cauchy_gamma)
    invk1 = (1 :: Double) / fromIntegral k1
    samples = map ((invk1 *) . fromIntegral) [0..k1-1] ++ map ((\ i -> exp (invk1 * i)) . fromIntegral) [0..k2*k1]
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

performLocalSensitivityAnalysis :: Bool -> Map CatName [(CatName, CatName)] -> QueryExpr -> IO ()
performLocalSensitivityAnalysis debug schema query = do
  putStrLn "performLocalSensitivityAnalysis"
  putStrLn "Processing the schema"
  origTableCols <- fmap Map.fromList $ forM (Map.toList schema) $ \ (n1,ns) -> do
    let tblName = T.unpack n1
    let cols = map (T.unpack . fst) ns
    return (tblName, cols)
  _ <- performLocalSensitivityAnalysis' debug origTableCols query
  return ()

performLocalSensitivityAnalysis' :: Bool -> Map String [String] -> QueryExpr -> IO ([String], Table, [([(String, Int)], [([Int], [Int], [Int])])])
performLocalSensitivityAnalysis' debug origTableCols query = do
  let wheres = extractWhereExpr query
  putStrLn "performLocalSensitivityAnalysis'"

  putStrLn "Processing FROM clause"
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
        (subColNames, res, ders) <- performLocalSensitivityAnalysis' debug origTableCols subquery
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
  let origTableName = (Map.fromList (zip tableNames origTableNames) Map.!)
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

  putStrLn "Processing SELECT clause"
  let
    cse = compileScalarExpr (nmcsToAddr . nmcs)
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
    (sumExprs0,groupExprs) =
      partitionEithers eithers
    -- assemble a query result row from the values of sumExprs and groupExprs
    assembleResult0 ss gs = f eithers ss gs where
      f [] [] [] = []
      f (Left _ : es) (s : ss) gs = s : f es ss gs
      f (Right _ : es) ss (g : gs) = g : f es ss gs
    numGroupExprs = length groupExprs
    numExprs = length sumExprs0 + numGroupExprs
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
    numSumExprs = length sumExprs
  printf "Selected column names: %s\n" (show selectedColNames)

  putStrLn "Processing WHERE clause"
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
  forM_ wheres processWhere
  wheresForAddr <- freeze wheresForAddrArr :: IO (Array Int [ScalExpr])
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
    printDerivatives ders = when debug $ do
      forM_ ders $ \ (els',vs,d) ->
        printf "    %s -> %s -> %s\n" (show els') (show vs) (show d) :: IO ()

    -- dtables must be in ascending order
    findDerivatives dtables = do
      when debug $ putStr "Finding derivatives w.r.t. tables "
      when debug $ print (map tableName dtables)
      let numdtables = length dtables
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
      derivatives <- newIORef Map.empty :: IO (IORef (Map ([Int],[Int]) [Int]))
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
        return (gels,vs,d)

    crossProd [] = [[]]
    crossProd (xs:yss) = [x : ys | x <- xs, ys <- crossProd yss]

    combins k xs = f (length xs) k xs where
      f _ 0 _ = [[]]
      f n k ~(x : xs)
        | n >= k    = f (n-1) k xs ++ (map (x :) $ f (n-1) (k-1) xs)
        | otherwise = []

    subsets [] = [[]]
    subsets (x : xs) = let ss = subsets xs in ss ++ (map (x :) ss)

    -- A pattern is either the null pattern or a list of nonnegative integers where 0 matches any positive integer
    -- e.g. [2,0,3,0] matches all lists [2,i,3,j] where i and j are any positive integers
    -- The null pattern does not match anything
    -- The zero pattern is a list whose all elements are 0, i.e. it matches everything
    -- We define the partial order on patterns as the subset relation on the sets they match,
    -- i.e. the null pattern is the smallest and the zero pattern is the largest
    -- The intersection of a set of patterns P matches the lists matched by all patterns in P
    -- A pattern map is mapping from a set of patterns to integers
    -- A closed pattern set is a set of patterns P such that P+{null pattern} is closed under intersection and P contains the zero pattern
    -- A closed pattern map is mapping from a closed pattern set to integers
    -- We merge two closed pattern maps cpm1 and cpm2 to get a new closed pattern map cpm such that
    -- if p is the intersection of a pattern mapped by cpm1 and a pattern mapped by cpm2 then
    -- cpm(p) = cpm1(p1) + cpm2(p2) | p <= p1 & p <= p2}
    -- where p1 is the intersection of all patterns p1 mapped by cpm1 such that p <= p1
    --       (i.e. the smallest pattern p1 mapped by cpm1 such that p <= p1)
    -- and   p2 is the intersection of all patterns p2 mapped by cpm2 such that p <= p2
    --       (i.e. the smallest pattern p2 mapped by cpm2 such that p <= p2)
    -- The arguments to mergeCpms are given as sorted association lists
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

    derMapCrossProd [dm] = dm
    derMapCrossProd (dm : dms) = [(e1 ++ e2, v1 ++ v2, [d1 * d2]) | let dmcp = derMapCrossProd dms, (e1,v1,[d1]) <- dm, (e2,v2,[d2]) <- dmcp]

    permuts xs = f (length xs) xs where
      insert x 0 ys = x : ys
      insert x k (y:ys) = y : insert x (k-1) ys
      f 0 [] = [[]]
      f n (x:xs) = [insert x k p | p <- f (n-1) xs, k <- [0..n-1]]

    splitUnassembledElsVs (els,d) = (els',vs,d) where
      (els',vs) = splitAt (length els - numGroupExprs) els

    splitElsVs (els,d) = (els',vs,d) where
      (els',vs) = splitAt (length els - numAssembledVs) els

    unsplitElsVs (els,vs,d) = (els ++ vs, d)

    -- dtncs contains a list of pairs of a table and the number of times to differentiate w.r.t. that table
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
    --queryResult = concat $ zipWith assembleResult ds vss
      --where (_,vss,ds) = unzip3 queryResult0
    queryResult = concatMap getResult queryResult0
      where getResult ([],vs,[d]) = replicate d vs
  let canComputeNoiseLevel = numGroupExprs == 0 && numSumExprs == 1
  let
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

    showNoiseLevelList :: [Double] -> String
    showNoiseLevelList [] = "[]"
    showNoiseLevelList nls = take (length s - 3) s
      where s = concatMap (printf "%0.3f | " :: Double -> String) nls
  ders3 <- if hasSubQueries then combineSubQueryDers else return derivatives
  nlss <- fmap transpose $ forM ders3 $ \ (dtncs,ders) -> do
    putStr "Combined derivatives w.r.t. original tables "
    print dtncs
    let ders4 = map splitElsVs $ mergeManyCpms (map ((:[]) . unsplitElsVs) ders)
    let numdtables = sum (map snd dtncs)
    let
      nlm :: Double -> Double -> Double
      nlm noise_C1 noise_C2 = if numdtables == 0 then 0 else noise_C2 / noise_b2 * (noise_C1 / noise_b1)^(numdtables - 1) / noise_epsilon^numdtables
      --nlmC = nlm noise_Cauchy_C1 noise_Cauchy_C2
      --nlmL = nlm noise_Laplace_C1 noise_Laplace_C2

      distr_nlm :: NoiseDistribution -> Double
      distr_nlm d = nlm (distrC1 d) (distrC2 d)
    let distr_nlms = map distr_nlm noise_distributions
    when canComputeNoiseLevel $ printf "Noise level multiplier = %s\n" (showNoiseLevelList distr_nlms)
    maxd <- fmap maximum $ forM ders4 $ \ (els',vs,d) -> do
      let d1 = if null d then 1 else head d
      --let nlC = nlmC * fromIntegral d1
      --let nlL = nlmL * fromIntegral d1
      --if canComputeNoiseLevel
      --  then printf "%s -> %s -> %s -> noise level %0.3f | %0.3f\n" (show els') (show vs) (show d) nlC nlL
      --  else printf "%s -> %s -> %s\n" (show els') (show vs) (show d)
      printf "%s -> %s -> %s\n" (show els') (show vs) (show d)
      --return nl
      return (fromIntegral d1)
    let nls = map (* maxd) distr_nlms
    --let nlC = nlmC * maxd
    --let nlL = nlmL * maxd
    when canComputeNoiseLevel $ printf "-> noise level %s\n" (showNoiseLevelList nls)
    --when canComputeNoiseLevel $ printf "-> noise level %0.3f | %0.3f\n" nlC nlL
    --return (nlC,nlL)
    return nls
  --let noiseLevelC = maximum nlsC
  --let noiseLevelL = maximum nlsL
  let noiseLevels = map maximum nlss
  if canComputeNoiseLevel
    then do
      --nqsGC <- compute_generalized_Cauchy_distribution
      printf "query result = %0.3f\n" (fromIntegral (head (head queryResult)) :: Double)
      --printf "noise level to add = %0.3f | %0.3f\n" noiseLevelC noiseLevelL
      printf "noise level to add = %s\n" (showNoiseLevelList noiseLevels)
      -- quantiles of the absolute value of added noise
      --let nqL p = - log (1 - p)
      --when (noise_Cauchy_gamma == 2) $ do
      do
        --let nqC p = tan (0.5 * pi * p)
        let ps = 0 : 0.001 : 0.01 : 0.1 : 0.2 : 0.3 : 0.4 : map (\ i -> 1 - (2 :: Double)**(- 1.0 * i)) [1..20]
        let nqss = transpose $ map (flip distrQuantiles ps) noise_distributions
        forM_ (zip ps nqss) $ \ (p, nqs) -> do
          let qs = zipWith (*) noiseLevels nqs
          --let qC = noiseLevelC * nqC p
          --let qL = noiseLevelL * nqL p
          --printf "%9.5f%% quantile: %0.3f %0.3f | %0.3f | ratio = %0.3f\n" (100 * p) (noiseLevelC * nqGC) qC qL (qC / qL)
          printf "%9.5f%% quantile: %s\n" (100 * p) (showNoiseLevelList qs)
    else do
      putStrLn "query result:"
      mapM_ print queryResult
  return (selectedColNames, queryResult, derivatives)
