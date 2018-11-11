module LocalSensitivity (performLocalSensitivityAnalysis) where

import Control.Monad
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Map (Map)
import Data.Set (Set)
import Data.Array.IArray
import Data.Array.Unboxed
import Data.Array.MArray
import Data.Array.IO
import Data.IORef
import Data.Char
import Data.Either
import Data.Maybe
import Data.List
import System.IO
import Debug.Trace
import Text.Printf
import Database.HsSqlPpp.Catalog
import Database.HsSqlPpp.Syntax
import Database.HsSqlPpp.Pretty
import Database.HsSqlPpp.Dialect
import Database.HDBC
import SelectQuery
import ProgramOptions
import DatabaseQ

type Table = [[Int]]
type Database = [Table]

-- type of derivatives
type DerT = Double

combinedSensitivityTmpFileName = "_combined_sensitivity.tmp"

sqlDialect = postgresDialect
prettyFlags = PrettyFlags {ppDialect = sqlDialect}
showScalarExpr = TL.unpack . prettyScalarExpr prettyFlags
showQuery = TL.unpack . prettyQueryExpr prettyFlags

--sumExprBound = 1000

minExprBound = 0
maxExprBound = 1000

data NoiseParameters =
  NoiseParameters {
    noise_epsilon :: Double,
    noise_b2 :: Double, -- must be in the interval (0,1)
    noise_beta :: Maybe Double
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
    distrBeta = \ np -> case noise_beta np of Just beta -> beta; Nothing -> noise_b1 np * noise_epsilon np / (noise_Cauchy_gamma + 1),
    distrSmNlm = \ np -> case noise_beta np of Just beta -> noise_b1 np / (noise_b2 np * beta)
                                               Nothing -> (noise_Cauchy_gamma + 1) / (noise_b2 np * noise_epsilon np),
    distrC1 = noise_Cauchy_C1,
    distrC2 = noise_Cauchy_C2,
    distrQuantiles = compute_generalized_Cauchy_distribution_quantiles noise_Cauchy_gamma
  }
  where
    noise_Cauchy_C1 = 1 + noise_Cauchy_gamma
    noise_Cauchy_C2 = 1 + noise_Cauchy_gamma

--noise_distributions = [noise_GenCauchy 10.0, noise_GenCauchy 4.0, noise_GenCauchy 3.0, noise_Cauchy, noise_Laplace 1.0e-5, noise_Laplace 1.0e-10]
noise_distributions = [noise_GenCauchy 4.0]

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


instance Ord SqlValue where
  compare (SqlString x1) (SqlString x2) = compare x1 x2
  compare (SqlByteString x1) (SqlByteString x2) = compare x1 x2
  compare (SqlChar x1) (SqlChar x2) = compare x1 x2
  compare (SqlInteger x1) (SqlInteger x2) = compare x1 x2
  compare (SqlInt64 x1) (SqlInt64 x2) = compare x1 x2
  compare (SqlInt32 x1) (SqlInt32 x2) = compare x1 x2
  compare (SqlDouble x1) (SqlDouble x2) = compare x1 x2
  compare (SqlRational x1) (SqlRational x2) = compare x1 x2
  compare (SqlBool x1) (SqlBool x2) = compare x1 x2

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
mergeCpms :: [([SqlValue],[DerT])] -> [([SqlValue],[DerT])] -> [([SqlValue],[DerT])]
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
        (SqlNull,cpm):mgb -> (cpm, mgb)
        _ -> ([], mgb1)
    (c20,m2) =
      case mgb2 of
        (SqlNull,cpm):mgb -> (cpm, mgb)
        _ -> ([], mgb2)
    mapfun (ys,n) = (SqlNull:ys, n)
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

mergeManyCpms :: [[([SqlValue],[DerT])]] -> [([SqlValue],[DerT])]
mergeManyCpms [] = []
mergeManyCpms [cpm] = cpm
mergeManyCpms cpms =
  let
    (cpms1,cpms2) = splitAt (length cpms `div` 2) cpms
  in
    mergeCpms (mergeManyCpms cpms1) (mergeManyCpms cpms2)

--patternIntersection :: Maybe [Int] -> Maybe [Int] -> Maybe [Int]
--patternIntersection Nothing _ = Nothing
--patternIntersection _ Nothing = Nothing
--patternIntersection (Just p1) (Just p2) = patternIntersection' p1 p2
--
--patternIntersection' :: [Int] -> [Int] -> Maybe [Int]
--patternIntersection' [] [] = Just []
--patternIntersection' (0 : xs) (y : ys) = (y :) <$> patternIntersection' xs ys
--patternIntersection' (x : xs) (0 : ys) = (x :) <$> patternIntersection' xs ys
--patternIntersection' (x : xs) (y : ys) | x == y    = (x :) <$> patternIntersection' xs ys
--                                       | otherwise = Nothing
--
--isPatternSubset :: [Int] -> [Int] -> Bool
--isPatternSubset [] [] = True
--isPatternSubset (x : xs) (0 : ys) = isPatternSubset xs ys
--isPatternSubset (x : xs) (y : ys) = x == y && isPatternSubset xs ys
--
--derMapCrossProd :: [[([Int], [Int], [DerT])]] -> [([Int], [Int], [DerT])]
--derMapCrossProd [dm] = dm
--derMapCrossProd (dm : dms) = [(e1 ++ e2, v1 ++ v2, [d1 * d2]) | let dmcp = derMapCrossProd dms, (e1,v1,[d1]) <- dm, (e2,v2,[d2]) <- dmcp]


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

data AggrOp = AggrCount | AggrSum | AggrMin | AggrMax
  deriving Eq

instance Show AggrOp where
  show AggrCount = "COUNT"
  show AggrSum = "SUM"
  show AggrMin = "MIN"
  show AggrMax = "MAX"

scalarExprAddrs :: (Name -> Int) -> ScalarExpr -> [Int]
scalarExprAddrs nta = nub . f where
  f (BooleanLit _ b) = []
  f (NumberLit _ s) = []
  f (StringLit _ s) = []
  f (Identifier _ ns) = [nta ns]
  f (BinaryOp _ ns e1 e2) = f e1 ++ f e2
  f (App _ n es) = concatMap f es
  f (Cast _ e _) = f e
  -- TODO alisa added Parens temporarily
  f (Parens _ e) = f e
  f e = error $ "scalarExprAddrs: " ++ show e


showNoiseLevelList :: [Double] -> String
showNoiseLevelList [] = "[]"
showNoiseLevelList nls = take (length s - 3) s
  where s = concatMap (printf "%0.3f | " :: Double -> String) nls

showNoiseLevelList2 :: [Double] -> String
showNoiseLevelList2 [] = "[]"
showNoiseLevelList2 nls = take (length s - 3) s
  where s = concatMap (printf "%9.3f | " :: Double -> String) nls

performLocalSensitivityAnalysis :: ProgramOptions -> Map CatName [(CatName, CatName)] -> QueryExpr -> IO ()
performLocalSensitivityAnalysis args schema query = do
  putStrLn "performLocalSensitivityAnalysis"
  putStrLn "Processing the schema"
  (tblNames, colss, typess) <- fmap unzip3 $ forM (Map.toList schema) $ \ (n1,ns) -> do
    let tblName = T.unpack n1
    printf "table %s\n" tblName
    let cols = map (T.unpack . fst) ns
    let types = map (T.unpack . snd) ns
    forM_ ns $ \ (c,t) -> printf "  %s: %s\n" (T.unpack c) (T.unpack t)
    return (tblName, cols, types)
  let origTableCols = Map.fromList $ zip tblNames colss
  let origTableTypes = Map.fromList $ zip tblNames typess
  let np = NoiseParameters { noise_epsilon = 1, noise_b2 = 0.5, noise_beta = getBeta args }
  printf "beta = %s\n" (show (noise_beta np))
  (writeCombinedOutput, maybeTmpHandle) <-
    if combinedSens args
      then do
        h <- openFile combinedSensitivityTmpFileName WriteMode
        return (hPutStrLn h, Just h)
      else
        return (const (return ()), Nothing)
  --forM_ [0.1,0.2..0.9] $ \ b2 -> do
  --  _ <- performLocalSensitivityAnalysis' debug np{noise_b2 = b2} origTableCols query
  --  return ()
  _ <- performLocalSensitivityAnalysis' args writeCombinedOutput np origTableCols origTableTypes query
  case maybeTmpHandle of
    Just h -> hClose h
    Nothing -> return ()
  return ()

parseCommaSeparatedList :: String -> [String]
parseCommaSeparatedList [] = []
parseCommaSeparatedList s = f [] s where
  f [] [] = []
  f a [] = [reverse a]
  f a (',':s) = reverse a : f [] s
  f a (c:s) = f (c:a) s

parseColonPair :: String -> (String,String)
parseColonPair s = f [] s where
  f a [] = (reverse a, "")
  f a (':':s) = (reverse a, s)
  f a (c:s) = f (c:a) s

performLocalSensitivityAnalysis' :: ProgramOptions -> (String -> IO ()) -> NoiseParameters -> Map String [String] -> Map String [String] -> QueryExpr -> IO ([String], Table, [([(String, Int)], [([Int], [Int], [DerT])])])
performLocalSensitivityAnalysis' args writeCombinedOutput np origTableCols origTableTypes query = do
  let debug = debugVerbose args
  putStrLn "performLocalSensitivityAnalysis'"
  putStrLn (showQuery query)

  let sumExprBound = getSumExprBound args

  let forbiddenCols = Set.fromList $ parseCommaSeparatedList (forbidden args)
  printf "forbiddenCols = %s\n" (show forbiddenCols)

  let tableGlist = parseCommaSeparatedList (tableGs args)
  let tableGmap = Map.fromList $ map (\ tg -> case parseColonPair tg of
                                                (tbl,"") -> (tbl,(1::Double)/0)
                                                (tbl,g)  -> (tbl,read g::Double))
                                     tableGlist
  printf "tableGmap = %s\n" (show tableGmap)

  putStrLn "Processing FROM clause"
  (hasSubQueries,allSubQueryDers,tableName,tableNames,colNamess,origTableNames,origTableIds,newTableIds,origTables,newTableCount,numCols,tblAddr,addrToTbl,addrToTblCol,addrToColType,nmcsToAddr,totalNumCols,colEq,numTables,forbiddenAddrs) <- do
    let tmpTableName = ('$' :)
    (tableNames, origTableNames, colNamess, colTypess, derss) <- fmap unzip5 $ forM (selTref query) $ \ tr -> do
      case tr of
        Tref _ n -> do
          let tblName = head (nmcs n)
          printf "%s -> %s\n" tblName tblName
          return (tblName, tblName, origTableCols Map.! tblName, origTableTypes Map.! tblName, Nothing)
        TableAlias _ newTblName0 (Tref _ n) -> do
          let newTblName = ncStr newTblName0
          let origTblName = head (nmcs n)
          printf "%s -> %s\n" origTblName newTblName
          return (newTblName, origTblName, origTableCols Map.! origTblName, origTableTypes Map.! origTblName, Nothing)
        TableAlias _ newTblName0 (SubTref _ subquery) -> do
          let newTblName = ncStr newTblName0
          putStrLn "Processing subquery"
          putStrLn "==================="
          (subColNames, res, ders) <- performLocalSensitivityAnalysis' args writeCombinedOutput np origTableCols origTableTypes subquery
          putStrLn "============================"
          putStrLn "Finished processing subquery"
          printf "-> %s\n" newTblName
          return (newTblName, tmpTableName newTblName, subColNames, undefined, Just ders)
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
    let origTableNameToId = (Map.fromList (zip origTables [0..]) Map.!)
    let origTableIds = map origTableNameToId origTableNames
    putStr "Tables: "
    print tableNames
    putStr "Original tables: "
    print origTables
    putStr "Original table IDs of selected tables: "
    print origTableIds
    let newTableCount = length . newTableIds
    let colId = (Map.fromList (zip tableNames (map (\ colNames -> (Map.fromList (zip colNames [0..]) Map.!)) colNamess)) Map.!)
    let numCols = (Map.fromList (zip [0..] (map length colNamess)) Map.!)
    let nmcsToColId [tn,cn] = (tableId tn, colId tn cn)
    let tblAddr = listArray (0,numTables) (prefixSum (map numCols [0..numTables-1])) :: UArray Int Int
    let nmcsToAddr ns = let (ti,ci) = nmcsToColId ns in (tblAddr ! ti) + ci
    let totalNumCols = tblAddr ! numTables
    let addrToTbl = listArray (0,totalNumCols-1) (concatMap (\ i -> replicate (numCols i) i) [0..numTables-1]) :: UArray Int Int
    let addrToTblColList = [(t,c) | (t,cs) <- zip tableNames colNamess, c <- cs]
    let addrToTblCol = listArray (0,totalNumCols-1) addrToTblColList :: Array Int (String,String)
    let forbiddenAddrs = Set.fromList [i | (i,(t,c)) <- zip [0..] addrToTblColList, (t ++ '.' : c) `Set.member` forbiddenCols]
    putStr "forbiddenAddrs: "
    print forbiddenAddrs
    let addrToColType = listArray (0,totalNumCols-1) [ct | (t,cts) <- zip tableNames colTypess, ct <- cts] :: Array Int String
    putStr "addrToTblCol: "
    print addrToTblCol
    putStr "addrToColType: "
    print addrToColType
    colEq <- newArray ((0,0), (totalNumCols-1,totalNumCols-1)) False :: IO (IOUArray (Int,Int) Bool)
    return (hasSubQueries,allSubQueryDers,tableName,tableNames,colNamess,origTableNames,origTableIds,newTableIds,origTables,newTableCount,numCols,tblAddr,addrToTbl,addrToTblCol,addrToColType,nmcsToAddr,totalNumCols,colEq,numTables,forbiddenAddrs)

  let containsForbiddenAddrs as = not $ Set.null (Set.intersection (Set.fromList as) forbiddenAddrs)

  putStrLn "Processing SELECT clause"
  let
    (selectedColNames,groupExprs,numGroupExprs,uncompiledSumExprs,minMaxExprs,aggrOps,minMaxAggrOps,assembleDer,numAssembledVs,numSumExprs) =
      (selectedColNames,groupExprs,numGroupExprs,uncompiledSumExprs,minMaxExprs,aggrOps,minMaxAggrOps,assembleDer,numAssembledVs,numSumExprs)
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
                        if countQuery args
                          then (NumberLit undefined "1", AggrCount)
                          else
                            case aggrOp ns of
                              "count" -> (NumberLit undefined "1", AggrCount)
                              "sum" -> (e1, AggrSum)
                              "min" -> (e1, AggrMin)
                              "max" -> (e1, AggrMax)
                    SelectItem _ e1 _ ->
                      Right $
                        e1
                )
        (sumExprs00,groupExprs) =
          partitionEithers eithers
        sumExprs0 = filter ((`elem` [AggrCount, AggrSum]) . snd) sumExprs00
        --sumExprs0 = map fst sumExprs00
        --uncompiledSumExprs = map snd sumExprs00
        (uncompiledSumExprs,aggrOps) = unzip sumExprs0
        sumExprsMinMax = filter ((`elem` [AggrMin, AggrMax]) . snd) sumExprs00
        (minMaxExprs,minMaxAggrOps) = unzip sumExprsMinMax
        numGroupExprs = length groupExprs
        (assembleDer,numAssembledVs) =
          if null uncompiledSumExprs
            then
              if selDistinct query == All
                then (id, numGroupExprs)
                else (\ (els,vs,[]) -> (els,vs,[1::DerT]), numGroupExprs)
            else
              if null groupExprs
                then (id, numGroupExprs)
                else (\ (els,vs,d) -> (els,assembleResult0 (map (const SqlNull) d) vs,[2]), numExprs)
          where
            numExprs = length uncompiledSumExprs + numGroupExprs
            -- assemble a query result row from the values of sumExprs and groupExprs
            assembleResult0 ss gs = f eithers ss gs where
              f [] [] [] = []
              f (Left _ : es) (s : ss) gs = s : f es ss gs
              f (Right _ : es) ss (g : gs) = g : f es ss gs
        numSumExprs = length uncompiledSumExprs

  printf "minMaxAggrOps = %s\n" (show minMaxAggrOps)

  let
    findQueryForMinMax aggrOp e1 =
        "SELECT " ++ intercalate ", " ((showScalarExpr e1 ++ " AS _value") : map (++ ".ID") tableNames) ++
        " FROM " ++ intercalate ", " (zipWith (\ ot t -> ot ++ " AS " ++ t) origTableNames tableNames) ++
        (if null dwheresList then "" else " WHERE ") ++ intercalate " AND " dwheresList ++
        " ORDER BY _value" ++ if aggrOp == AggrMin then "" else " DESC"
      where
        dwheresList = map showScalarExpr $ extractWhereExpr query


  let distrBetas = map (`distrBeta` np) noise_distributions

  nls2 <- if not (null minMaxExprs)
    then do
      let canComputeSmoothNoiseLevel = numGroupExprs == 0 && numSumExprs == 0 && length minMaxExprs == 1
      fmap head $ forM (zip minMaxAggrOps minMaxExprs) $ \ (aggrOp,e) -> do
        let q = findQueryForMinMax aggrOp e
        putStrLn q
        res <- sendQueryToDb args q
        rms0 <- forM res $ \ (r:rs) -> do
          let r' = fromSql r :: Double
          let rs' = map fromSql rs :: [Int]
          let rs'' = zip origTableIds rs'
          --putStrLn $ show r' ++ " " ++ show rs''
          let r'' = case aggrOp of AggrMin -> r' - minExprBound; AggrMax -> maxExprBound - r'
          when debug $ putStrLn $ show r'' ++ " " ++ show rs''
          return (r'', rs'')
        let
          process [] sms _ = return sms
          process ((r,s):rms) sms removedRows = do
            let n = Set.size removedRows
            let smsatds = map (\ beta -> r * exp (-beta * fromIntegral n)) distrBetas
            when debug $ printf "%0.3f %d %s %s\n" r n (show smsatds) (show $ Set.elems removedRows) :: IO ()
            process rms (zipWith max sms smsatds) (Set.fromList s `Set.union` removedRows)
        let rms1 = rms0 ++ [(maxExprBound - minExprBound, [])]
        sms1 <- process rms1 (map (const 0) distrBetas) Set.empty
        let r1 = fst (head rms1)
        let rms2 = map (\ (r,s) -> (r - r1, s)) (tail rms1)
        sms2 <- process rms2 sms1 Set.empty
        printf "smooth sensitivity (w.r.t. all tables combined): %s\n" (showNoiseLevelList sms2)
        when canComputeSmoothNoiseLevel $ printf "smooth sensitivity (with gamma = 4) w.r.t. all tables combined: %0.3f\n" (sms2 !! 0)
        let distr_smnlms = map (`distrSmNlm` np) noise_distributions
        let smnls = zipWith (*) sms2 distr_smnlms
        when canComputeSmoothNoiseLevel $ printf "-> smooth noise level %s\n" (showNoiseLevelList smnls)
        return smnls
    else do
      let aggrExprBound = case aggrOps of [AggrCount] -> 1
                                          _           -> sumExprBound

      printf "Selected column names: %s\n" (show selectedColNames)

      sumExprsAndTables <- forM uncompiledSumExprs $ \ se -> do
        putStrLn $ showScalarExpr se
        let as = scalarExprAddrs (nmcsToAddr . nmcs) se
        let tables = nub $ map (addrToTbl !) as
        print as
        print tables
        let se' = if containsForbiddenAddrs as then NumberLit undefined (show sumExprBound) else se
        return (se',tables)

      putStrLn "Processing WHERE clause"

      wheresAndTables <- do
        let
          processWhere w =
            case w of
              BinaryOp _ n (Identifier _ n1) (Identifier _ n2) | nmcs n == ["="] -> do
                let na1 = nmcsToAddr $ nmcs n1
                let na2 = nmcsToAddr $ nmcs n2
                unless (containsForbiddenAddrs [na1,na2]) $
                  writeArray colEq (na1,na2) True :: IO ()
                return []
              BinaryOp _ n w1 w2 | nmcs n == ["and"] -> do
                r1 <- processWhere w1
                r2 <- processWhere w2
                return (r1 ++ r2)
              _ -> do
                putStrLn $ TL.unpack $ prettyScalarExpr prettyFlags w
                let as = scalarExprAddrs (nmcsToAddr . nmcs) w
                let tables = nub $ map (addrToTbl !) as
                print as
                print tables
                return $ if containsForbiddenAddrs as then [] else [(w,tables)]
        let wheres = extractWhereExpr query
        wheresAndTables <- fmap concat $ forM wheres processWhere
        return wheresAndTables

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

      colEqComponents <- fmap concat $ forM [0..totalNumCols-1] $ \ i -> do
        eqs <- fmap concat $ forM [0..totalNumCols-1] $ \ j -> do
          b <- readArray colEq (i,j)
          return $ if b then [j] else []
        return $ if head eqs == i then [eqs] else []
      putStr "colEqComponents: "
      print colEqComponents

      let
        smootheRow1 d1 rowcounts0 rowcounts prices beta = do
          let missingSum = product rowcounts0 * aggrExprBound - d1
          let
            -- rowcount' * price * beta' = 1
            rcs' beta' = [max rowcount rowcount' | (rowcount,price) <- zip rowcounts prices, let rowcount' = 1/(price*beta')]
            f beta' = beta * (1 - missingSum / (product (rcs' beta') * aggrExprBound))
            g x1 x2 | x2-x1 < beta * 1e-10 = x1
                    | f x3 < x3            = g x1 x3
                    | otherwise            = g x3 x2
              where x3 = (x1+x2)*0.5
          let beta' = g 0 beta
          --let beta' = 0.5*beta
          let rowcounts' = rcs' beta'
          let cost = sum [(rc'-rc)*p | (rc,rc',p) <- zip3 rowcounts rowcounts' prices, not (isInfinite p)]
          let smsens = (product rowcounts' * aggrExprBound - missingSum) * exp (-cost*beta)
          --printf "rowcounts0=%s rowcounts=%s prices=%s d1=%0.6f beta=%0.6f beta'=%0.6f f(beta')=%0.6f cost=%0.6f smsens=%0.6f rowcounts'=%s\n" (show rowcounts0) (show rowcounts) (show prices) d1 beta beta' (f beta') cost smsens (show rowcounts') :: IO ()
          return smsens

        --smootheRow d1 sds prices = (smootheRowInt d1 sds >>= print) >> mapM (smootheRow1 d1 sds prices) distrBetas
        smootheRow d1 sds0 sds prices = mapM (smootheRow1 d1 sds0 sds prices) distrBetas

        smootheRowInt d1 sds = do
          -- TODO: allow xs to be floating-point numbers
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
          let xs = map round $ sort sds
          let satd0 k xs = product (map (fromIntegral :: Int -> Double) (satds k xs)) * aggrExprBound
          let numMissingRows = satd0 0 xs - d1
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
          --let betas = map (`distrBeta` np) noise_distributions
          --printf "  beta = %s\n" (showNoiseLevelList betas)
          --printf "  1/beta = %s\n" (showNoiseLevelList (map (1/) betas))
          --let beta = head distrBetas
          --forM_ [0..10] $ \ i ->
          --  printf "  %2d: %20s %10.3f %10.3f\n" i (show (satds i xs)) (satd i xs) (smsens0 beta i xs)
          putStr ""
          let smss = map (`smsens` xs) distrBetas
          return smss

      let
        findQueryForSmoothSensitivityDer dtable ti = --printf "Query for SmoothSensitivityDer (%d,%d):\n" dtable ti >>
                                                     findQueryForDerivativesGeneric includeWhereForTheseTables partitionColEqComp isTableNameIncluded distinguishCountsAndSums
          where
            -- (i,j) -> r -> the derivative of the count of table j (filtered by the where conditions) w.r.t. row r of table i
            tiName = tableName ti
            includeWhereForTheseTables tables = null tables || tables == [ti]
            partitionColEqComp as = (filter ((== dtable) . (addrToTbl !)) as, filter ((== ti) . (addrToTbl !)) as)
            isTableNameIncluded t = (t == tiName)
            distinguishCountsAndSums = False

        findQueryForDerivatives dtable = --printf "Query for derivatives w.r.t. table %s:\n" dtableName >>
                                         findQueryForDerivativesGeneric includeWhereForTheseTables partitionColEqComp isTableNameIncluded distinguishCountsAndSums
          where
            dtableName = tableName dtable
            includeWhereForTheseTables tables = dtable `notElem` tables
            partitionColEqComp = partition ((== dtable) . (addrToTbl !))
            isTableNameIncluded t = (t /= dtableName)
            distinguishCountsAndSums = True

        findQueryForDerivativesGeneric includeWhereForTheseTables partitionColEqComp isTableNameIncluded distinguishCountsAndSums = do
          let showTblCol (t,c) = t ++ '.' : c
          let showAddrCol = showTblCol . (addrToTblCol !)
          let
            wheres = concat $ flip map wheresAndTables $ \ (w,tables) ->
              if includeWhereForTheseTables tables
                then [w]
                else []
          let dwheres1 = flip map wheres showScalarExpr
          let
            (dwheress,dselectss) =
              unzip $ flip map colEqComponents $ \ as ->
                let (currAs,otherAs) = partitionColEqComp as
                    dwheres = if null otherAs then [] else zip otherAs (tail otherAs)
                    dselects = flip map currAs $ \ a ->
                      case otherAs of
                        [] -> (Nothing, a)
                        a2:_ -> (Just a2, a)
                in (dwheres,dselects)
          let dwheres2raw = concat dwheress
          let dwheres2 = map (\ (a1,a2) -> printf "%s = %s" (showAddrCol a1) (showAddrCol a2)) dwheres2raw
          let dselects = concat dselectss
          let dwheresList = dwheres1 ++ dwheres2
          let groupByList = intercalate ", " $ flip map dselects $ \ (b, a) -> let (t,c) = addrToTblCol ! a in '_' : c
          putStr ""
          return $
            "SELECT " ++
            (intercalate ", " $ (flip map dselects $ \ (b, a) ->
              (case b of Nothing -> "cast (null as " ++ (addrToColType ! a) ++ ")"; Just a2 -> showAddrCol a2) ++ " AS " ++ (let (t,c) = addrToTblCol ! a in '_' : c)) ++
              [case aggrOp of
                 AggrCount -> "COUNT(*)"
                 AggrSum | not distinguishCountsAndSums -> "COUNT(*)"
                 AggrSum | distinguishCountsAndSums -> show aggrOp ++ '(' : (if includeWhereForTheseTables tables then showScalarExpr se else show sumExprBound) ++ ")"
                 _ -> error ("Aggregation operation " ++ show aggrOp ++ " not supported")
               ++ " AS _derivative"
               | ((se,tables),aggrOp) <- zip sumExprsAndTables aggrOps]) ++
            " FROM " ++
            intercalate ", " (filter (not . null) $ zipWith (\ ot t -> if isTableNameIncluded t then ot ++ " AS " ++ t else "") origTableNames tableNames) ++
            (if null dwheresList then "" else " WHERE ") ++
            intercalate " AND " dwheresList ++
            " GROUP BY " ++ groupByList

        findBigQueryForDerivatives dtable = do
          let dtableName = tableName dtable
          let colNames = colNamess !! dtable
          d <- findQueryForDerivatives dtable
          ds <- forM (filter (/= dtable) [0..numTables-1]) (findQueryForSmoothSensitivityDer dtable)
          printf "Big query for derivatives w.r.t. table %s:\n" dtableName
          let
            bigQuery =
              "SELECT " ++
              intercalate ", " (map (\ cn -> "d._" ++ cn ++ " AS " ++ cn) colNames ++
                                "d._derivative AS _d" :
                                map (\ i -> 'd' : show i ++ "._derivative AS _d" ++ show i) [1..numTables-1]) ++
              " FROM " ++
              intercalate ", " (('(' : d ++ ") AS d") : zipWith (\ i d1 -> '(' : d1 ++ ") AS d" ++ show i) [1..] ds) ++
              " WHERE " ++
              intercalate " AND " ['(' : qcn ++ " = " ++ "d._" ++ cn ++ " OR " ++ qcn ++ " IS NULL)" | i <- [1..numTables-1], cn <- colNames, let qcn = 'd' : show i ++ "._" ++ cn]
          putStrLn bigQuery
          return bigQuery

        findDerivativesQ :: [Int] -> IO [([[SqlValue]], [SqlValue], [DerT])]
        findDerivativesQ [dtable] = do
          q <- findBigQueryForDerivatives dtable
          let dtableOrig = origTableIds !! dtable
          let otherTableOrigs = [ot | (t,ot) <- zip [0..numTables-1] origTableIds, t /= dtable]
          let localSensAddedRowCount = [if localSens args && ot == dtableOrig then 1 else 0 | (t,ot) <- zip [0..numTables-1] origTableIds, t /= dtable]
          --print localSensAddedRowCount
          let otherTableOrigNames = [ot | (t,ot) <- zip [0..numTables-1] origTableNames, t /= dtable]
          --print otherTableOrigNames
          let otherTableGs = map (Map.findWithDefault (getG args) `flip` tableGmap) otherTableOrigNames
          --print otherTableGs
          let tableUseCounts = map (\ ot -> length $ filter (== ot) otherTableOrigs) otherTableOrigs
          let prices = zipWith (/) otherTableGs $ map (fromIntegral :: Int -> Double) tableUseCounts
          --print tableUseCounts
          --print prices
          res <- sendQueryToDb args q
          let nc = numCols dtable
          if null res
            then do
              putStrLn "empty derivative"
              return [([replicate nc SqlNull], [], replicate (1 + length noise_distributions) 0)]
            else forM res $ \ rs -> do
              let (rs1,rs2) = splitAt nc rs
              let els = rs1
              --let els = flip map rs1 $ \ r -> case fromSql r :: Maybe Int of Just el -> el
              --                                                               Nothing -> 0
              let d = fromSql (head rs2) :: Double
              let ds = map fromSql (tail rs2) :: [Double]
              smss <- smootheRow d ds (zipWith (+) ds localSensAddedRowCount) prices
              printf "%s -> %f # %s # %s\n" (show els) d (show ds) (showNoiseLevelList smss)
              return ([els],[],d:smss)

      printf "distrSmNlm = %s\n" (showNoiseLevelList $ map (`distrSmNlm` np) noise_distributions)

      let
        printDerivatives :: [([Int], [Int], [DerT])] -> IO ()
        printDerivatives ders = when debug $ do
          forM_ ders $ \ (els',vs,d) ->
            printf "    %s -> %s -> %s\n" (show els') (show vs) (show d) :: IO ()

        splitUnassembledElsVs (els,d) = (els',vs,d) where
          (els',vs) = splitAt (length els - numGroupExprs) els

        splitElsVs (els,d) = (els',vs,d) where
          (els',vs) = splitAt (length els - numAssembledVs) els

        unsplitElsVs (els,vs,d) = (els ++ vs, d)

        -- dtncs contains a list of pairs of a table and the number of times to differentiate w.r.t. that table
        findDerivativesWrtOrigTables :: [(String,Int)] -> IO [([SqlValue], [SqlValue], [DerT])]
        findDerivativesWrtOrigTables dtncs = do
          when debug $ putStr "Finding derivatives w.r.t. original tables "
          when debug $ print dtncs
          ders3 <- fmap concat $ forM (crossProd $ map (\ (tn,c) -> combins c (newTableIds tn)) dtncs) $ \ tableIdss -> do
            let tableIds = concat tableIdss
            let sti = sort tableIds
            ders <- findDerivativesQ sti
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
          let ders5 = map assembleDer ders4
          --when debug $ putStrLn "ders5:"
          --printDerivatives ders5
          return ders5

        findAllDerivativesWrtOrigTables :: IO [([(String,Int)], [([SqlValue], [SqlValue], [DerT])])]
        findAllDerivativesWrtOrigTables =
          let
            --f []            [] = (\ x -> [([],x)]) <$> findDerivativesWrtOrigTables []
            f dtncs@[(_,1)] [] = (\ x -> [(dtncs,x)]) <$> findDerivativesWrtOrigTables dtncs
            f _             [] = return []
            f dtncs ((tn,ntc) : tncs) =
              fmap concat $ forM [0..ntc] $ \ i ->
                f (if i == 0 then dtncs else (tn,i) : dtncs) tncs
          in
            f [] (zip origTables (map newTableCount origTables))

      derivatives <- findAllDerivativesWrtOrigTables
      let canComputeNoiseLevel = numGroupExprs == 0 && numSumExprs == 1

      -- TODO: support subqueries for smooth sensitivity
      ders3 <- if hasSubQueries then error "Support of subqueries is currently broken" else return derivatives
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
        let distr_smnlms = map (`distrSmNlm` np) noise_distributions
        let canComputeSmoothNoiseLevel = canComputeNoiseLevel && numdtables == 1
        when canComputeSmoothNoiseLevel $ printf "Smooth noise level multiplier = %s\n" (showNoiseLevelList distr_smnlms)
        maxs <- fmap (map maximum . transpose) $ forM ders4 $ \ (els',vs,d) -> do
          let d1 = if null d then 1 else head d
          printf "%s -> %s -> %s\n" (show els') (show vs) (show d)
          if canComputeNoiseLevel && length d >= 1
            then return d
            else return [d1]
        let maxd:maxsmss = if null maxs then replicate (1 + length noise_distributions) 0 else maxs
        let smnls = zipWith (*) maxsmss distr_smnlms
        when canComputeSmoothNoiseLevel $ printf "-> smooth noise level %s\n" (showNoiseLevelList smnls)
        when canComputeSmoothNoiseLevel $ do
          let table = fst (head dtncs)
          let sens = maxsmss !! 0
          printf "smooth sensitivity (with gamma = 4) w.r.t. table %s: %0.3f\n" table sens
          writeCombinedOutput (table ++ " " ++ show sens)
        return $ if null smnls then replicate (length noise_distributions) 0 else smnls
      let noiseLevels = map maximum nlss
      let nls2 = noiseLevels
      return nls2

  queryResult <- sendQueryToDb args (showQuery query)

  if numGroupExprs == 0 && numSumExprs + length minMaxExprs == 1
    then do
      --printf "query result = %0.3f\n" (fromIntegral (head (head queryResult)) :: Double)
      printf "query result = %s\n" (case fromSql (head (head queryResult)) :: Maybe Double of Just r -> show r; Nothing -> "NULL")
      printf "noise level to add = %s\n" (showNoiseLevelList2 nls2)
      when (printQuantiles args) $ do
        -- quantiles of the absolute value of added noise
        let ps = 0 : 0.001 : 0.01 : 0.1 : 0.2 : 0.3 : 0.4 : map (\ i -> 1 - (2 :: Double)**(- 1.0 * i)) [1..20]
        let nqss = transpose $ map (flip distrQuantiles ps) noise_distributions
        forM_ (zip ps nqss) $ \ (p, nqs) -> do
          let qs2 = zipWith (*) nls2 nqs
          --printf "%9.5f%% quantile: %0.3f %0.3f | %0.3f | ratio = %0.3f\n" (100 * p) (noiseLevelC * nqGC) qC qL (qC / qL)
          printf "%9.5f%% quantile: %s\n" (100 * p) (showNoiseLevelList2 qs2)
    else do
      putStrLn "query result:"
      mapM_ print queryResult
  --return (selectedColNames, queryResult, derivatives)
  return undefined
