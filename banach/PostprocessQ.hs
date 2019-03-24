module PostprocessQ where

import Debug.Trace

import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import ProgramOptions
import Text.Printf
import ErrorMsg

import qualified Banach as B
import qualified BanachQ as BQ
import PolicyQ
import GroupQ

traceIOIfDebug :: Bool -> String -> IO ()
traceIOIfDebug debug msg = do
    if debug then traceIO msg
    else return ()

filterWith [] [] = []
filterWith (b:bs) (x:xs) =
    let ys = filterWith bs xs in
    if b then (x:ys) else ys

-- finds y such that y * exp(y) = x
lambert x 0 = 1
lambert x n =
    let an = lambert x (n - 1) in
    an - (an * exp(an) - x) / ((an + 1) * exp(an))

compute_epsilon :: Double -> Double -> Double -> Double -> Int -> Double
compute_epsilon delta a q p nq =

    -- we know that the probability cannot grow above 100%
    let d = min (1 - p) delta in
    - (log (p / (q - p) * (1 / (d + p) - 1))) / (a * fromIntegral nq)

compute_worst_epsilon :: Double -> Double -> Double -> Int -> Double
compute_worst_epsilon delta a q nq =
    2 / (a * fromIntegral nq) * (log ((sqrt q + sqrt (delta*(delta + q - 1))) / (1 - delta)))

compute_one_comb_data :: Int -> Double -> [[Double]] -> [[Bool]] -> [[Double]] -> [Maybe Double] -> [Maybe Double] -> (Double,Double,Double,Double)
compute_one_comb_data nq delta ass dss rrss qs' ps =

    -- compute data for each AND
    -- we take 2a as distance since X' may be located somewhere in a corner, except the discrete case
    let as' = map (foldr max 0) $ zipWith (zipWith (\d a -> if d then 1.0 else 2*a)) dss ass in
    let rrs = map (foldr max 0) rrss in

    -- determine the bounds
    let (qs,as) = unzip $ zipWith3 (\q a rr -> if q == Nothing then (1,rr) else (fromJust q, a)) qs' as' rrs in

    -- this is the information about the region within distance a
    let a = foldr max 0 as in
    let q = (product qs) in

    -- compute the epsilon (use worst-case p if p is unknown)
    if elem Nothing ps then 
        let eps = compute_worst_epsilon delta a q nq in
        let p = sqrt q * (exp (eps / 2) - sqrt q) / (exp eps - 1) in
        (a,eps,q,p)
    else
        let p   = (product qs) - (product $ zipWith (-) qs (map fromJust ps)) in
        let eps = compute_epsilon delta a q p nq in
        --trace (show qs) $
        --trace (show ps) $
        --trace (show (a,eps,q,p)) $
        --trace ("-------------") $
        (a,eps,q,p)

compute_data :: Double -> Double -> [[Double -> Maybe [Double]]] -> [[Bool]] -> [[Double]] -> [[Double]] -> Int -> (Double,Double,Double,Double)
compute_data delta starting_a gss dss rss rrss nq =

    -- adjust proposed a to the actual bounds R
    let ass = zipWith (zipWith (\d rr -> if d then rr else min rr starting_a)) dss rrss in

    -- compute the weights (some of them can be unknown)
    let qss = zipWith3 (zipWith3 (\g a r -> g (a*r))) gss ass rss in
    let pss = zipWith  (zipWith  (\g r   -> g r    )) gss rss in

    -- collect all possible variants of q and p
    let cqss = (map (map (\qs -> if elem Nothing qs then Nothing else Just $ product (map fromJust qs))) . allCombsOfLists . map allCombsOfMaybeLists) qss in
    let cpss = (map (map (\ps -> if elem Nothing ps then Nothing else Just $ product (map fromJust ps))) . allCombsOfLists . map allCombsOfMaybeLists) pss in
    let eps  = zipWith (compute_one_comb_data nq delta ass dss rrss) cqss cpss in

    let (a,epsilon,q,p) = foldr (\x1@(_,e1,_,_) x2@(_,e2,_,_) -> if e1 < e2 then x1 else x2) (head eps) (tail eps) in
    --trace ("ass: " ++ show ass) $
    --trace ("rss: " ++ show rss) $
    --trace ("qss: " ++ show qss) $
    --trace ("pss: " ++ show pss) $
    --trace ("eps: " ++ show eps) $
    --trace (show (a,epsilon,q,p)) $
    --trace ("-------------") $
    (a,epsilon,q,p)

optimal_a_epsilon :: Double -> Double -> [[Double -> Maybe [Double]]] -> [[Bool]] -> [[Double]] -> [[Double]] -> Double -> Double -> Double -> Double
                     -> Double -> Double -> Int -> (Double,Double,Double,Double)
optimal_a_epsilon _ _ _ _ _ _ a epsilon q p 0 _ _ = (a,epsilon,q,p)
optimal_a_epsilon delta r gss dss rss rrss a epsilon q p k n nq =

    -- compute the initial value for a
    let rr = foldr max 0 (concat rrss) in
    let starting_a = r + k * (rr - r) / n in
    let (a',epsilon',q',p') = compute_data delta starting_a gss dss rss rrss nq in

    --take the best values found so far
    let (a'',epsilon'',q'',p'') = if (epsilon' > epsilon) then (a',epsilon',q',p') else (a,epsilon,q,p) in
    optimal_a_epsilon delta r gss dss rss rrss a'' epsilon'' q'' p'' (k-1) n nq

-- TODO if we want to look for an optimal beta here using binary search, we will also need outputTableName here
performDPAnalysis :: ProgramOptions -> String -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> BQ.DataWrtTables -> M.Map String VarState -> [(String, Maybe Double)] -> [Int] -> IO ()
performDPAnalysis args outputTableName dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

  let debug = not (alternative args)
  let epsilon = getEpsilon args
  let beta    = getBeta args

  -- do not look for optimal beta if it has been specified by the user
  (qmap,taskAggrMap) <- case beta of
          Just _  -> performAnalysis args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts
          Nothing -> do
                         (_,q,tm,_) <- findBestBeta args outputTableName epsilon beta dataPath separator initialQuery colNames typeMap taskMap tableExprData attMap colTableCounts
                         return (q,tm)

  traceIOIfDebug debug ("===============================")
  traceIOIfDebug debug ("final qmap: " ++ (show qmap))
  traceIOIfDebug debug ("final taskAggr: " ++ (show taskAggrMap))

  let outMap = M.fromListWith (++) $ concat $ map (\key -> extractFinalResults (qmap ! key) (taskAggrMap ! key) key) (M.keys qmap)
  let outList = map (\((taskName,tableName), zs) -> (taskName,[(tableName,zs)])) $ M.toList outMap
  let taskList = M.toList $ M.fromListWith (++) outList

  let taskStr = 
          map (\(taskName,res) ->
               if alternative args then
                  taskName ++ [B.unitSeparator] ++ (intercalate [B.unitSeparator] $ concat $ map (\ (tableName, zs) ->
                      let (_,qrs,bs,sdss) = unzip4 zs in
                      let qr  = if length qrs == 1 then show (head qrs) else show qrs in
                      let err = combinedErrs qrs bs sdss in
                      let eta = if length qrs == 1 then show (head (combinedEtas bs sdss)) else show (combinedEtas bs sdss) in
                      let sds = combinedSdss sdss in
                      [tableName, show sds, qr, eta, show (err * 100)]) res)
               else
                 taskName ++ "\n" ++ (intercalate "\n" $ map (\ (tableName, zs) ->
                      let (_,qrs,bs,sdss) = unzip4 zs in
                      let qr = if length qrs == 1 then printf "%0.6f" (head qrs) else show qrs in
                      let err = combinedErrs qrs bs sdss in
                      let eta = if length qrs == 1 then printf "%0.6f" (head (combinedEtas bs sdss)) else show (combinedEtas bs sdss) in
                      let sds = combinedSdss sdss in
                      printf "%s: %0.6f\t %s\t %s\t %0.3f" tableName sds qr eta (err * 100)) res)

          ) taskList

  putStrLn $ intercalate (if alternative args then [B.unitSeparator2] else "\n\n") taskStr


performPolicyAnalysis :: ProgramOptions -> String -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> BQ.DataWrtTables -> [(M.Map String VarState, Double)] -> M.Map String VarState -> [Int] -> IO ()
performPolicyAnalysis args outputTableName dataPath separator initialQuery colNames typeMap taskMap tableExprData plcMaps attMap colTableCounts = do

  -- the input epsilon now works as delta, the upper bound on attacker's advantage
  let debug = not (alternative args)
  let delta = getEpsilon args
  let fixedBeta = getBeta args
  let nq = numOfQueries args -- this basically scales epsilon nq times, assuming that up to nq queries may be run on the same data

  -- process the policy and the attacker knowledge
  let plainTypeMaps = map (\(tname,tmap) -> map (\(x,y) -> (tname ++ [tsep] ++ x,y)) tmap) typeMap
  let plainTypeMap  = M.fromList $ concat plainTypeMaps

  -- we rather assume that there is one leak-statement per policy, but if there are many, all of them have the same delta and can be summed up
  let cost = sum $ map snd plcMaps

  --remove the special variables that are not needed
  let kwlen = length reservedSensRowsKeyword
  let plcMapData = map (M.filterWithKey (\varName _ -> length varName < kwlen || reverse (take kwlen (reverse varName)) /= reservedSensRowsKeyword) . fst) plcMaps

  let bss  = map (extract_bs attMap) plcMapData
  let gss    = zipWith filterWith bss $ map (extract_gs attMap) plcMapData
  let dss    = zipWith filterWith bss $ map (extract_ds attMap) plcMapData
  let rss    = zipWith filterWith bss $ map (extract_rs attMap) plcMapData
  let rrss'  = zipWith filterWith bss $ map (extract_Rs attMap plainTypeMap) plcMapData

  -- further, we assume r = 1 everywhere in each dimension
  let rrss = zipWith (zipWith (/)) rrss' rss --rescaled R
  let r = 1

  -- space dimensionality comes from the total number of sensitive variables
  -- we multiply the dimensions of variables belonging to one sensitive set
  -- we add the weights of different sensitive sets, since the attacker may guess any of them
  -- TODO do not include repeating variables multiple times into the intersection weight
  let allSensVars = S.fromList $ concat (map M.keys plcMapData)

  -- it seems that brute-forcing optimal epsilon and a works quite well
  -- we consider multidimensional space, where the radius is linf-norm
  let (init_a, init_epsilon, init_q, init_p) = compute_data delta (foldr max 0 (concat rrss)) gss dss rss rrss nq
  let num_of_tries = 10000
  let (a,epsilon,q,p) = optimal_a_epsilon delta r gss dss rss rrss init_a init_epsilon init_q init_p num_of_tries num_of_tries nq

  {-
  -- this computation works only for uniform distribtions
  -- convert guessing probability to epsilon (assuming that 'a' is optimal)
  let ub = p + d
  let es' = map (\r -> (lambert (ub / (exp(1) * (1 - ub))) 10) / r) rs
  -- consider scaled dimensions, where r = 1 for all r
  let epsilon' = if m == 1 then lambert (ub / (exp(1) * (1 - ub))) 10 else m / (exp(1) * (1 / ub - 1 + exp(-m)) ** (1 / m))

  -- find the initial (optimal) value of a
  -- we compute a = m / epsilon + 1 if m = 1, and m / epsilon for the multidimensional case
  let a' = if m == 1 then m / epsilon' + 1 else m / epsilon'
  -}

  traceIOIfDebug debug ("plcMaps: " ++ show plcMaps)
  traceIOIfDebug debug ("allSensVars: " ++ show allSensVars)
  traceIOIfDebug debug ("--------")
  traceIOIfDebug debug ("delta: " ++ (show delta))
  traceIOIfDebug debug ("--------")
  traceIOIfDebug debug ("rrss': " ++ (show rrss'))
  traceIOIfDebug debug ("rss: " ++ (show rss))
  traceIOIfDebug debug ("rrss: " ++ (show rrss))
  traceIOIfDebug debug ("r: " ++ (show r))
  traceIOIfDebug debug ("--------")
  traceIOIfDebug debug ("a: " ++ (show a))
  traceIOIfDebug debug ("eps: " ++ (show epsilon))
  traceIOIfDebug debug ("q: " ++ (show q))
  traceIOIfDebug debug ("p: " ++ (show p))

  let pr_pre  = p
  let pr_post = 1 / (1 + exp(- a * epsilon * (fromIntegral nq)) * (q-p) / p)

  (finalBeta,finalQmap,finalTaskAggr,finalError) <- findBestBeta args outputTableName epsilon fixedBeta dataPath separator initialQuery colNames typeMap taskMap tableExprData attMap colTableCounts

  traceIOIfDebug debug ("===============================")
  traceIOIfDebug debug ("final qmap: " ++ (show finalQmap))
  traceIOIfDebug debug ("final taskAggr: " ++ (show finalTaskAggr))

  let expectedCost = delta * cost
  traceIOIfDebug debug ("params: beta=" ++ (show finalBeta) ++ ", eps=" ++ (show epsilon))

  putStrLn $ intercalate (if alternative args then [B.unitSeparator2] else "\n\n") [show (pr_pre * 100.0), show (pr_post * 100.0), show expectedCost, show (finalError * 100.0)]
  {-
  -- TODO we want to output more values to the user in later UI versions
  putStrLn $ intercalate (if alternative args then [B.unitSeparator2] else "\n\n") [show (pr_pre * 100.0),
                                                                                    show (pr_post * 100.0),
                                                                                    show expectedCost,
                                                                                    show (finalError * 100.0),
                                                                                    show epsilon,
                                                                                    show finalBeta,
                                                                                    show finalSds]
  -}


findBestBeta :: ProgramOptions -> String -> Double -> Maybe Double -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> BQ.DataWrtTables -> M.Map String VarState -> [Int] -> IO (Double, M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double)
findBestBeta args outputTableName epsilon fixedBeta dataPath separator initialQuery colNames typeMap taskMap tableExprData attMap colTableCounts = do

  let step = performAnalysisBetaStep args outputTableName epsilon dataPath separator initialQuery colNames typeMap taskMap [] tableExprData attMap [] colTableCounts
  (finalBeta,finalQmap,finaltaskAggr,finalError) <- case fixedBeta of
                    Nothing -> do
                        initialBeta <- BQ.findMinimumBeta args epsilon Nothing dataPath separator initialQuery colNames typeMap [] tableExprData attMap [] colTableCounts
                        (initialQmap,initialTaskAggr,initialError) <- step (Just initialBeta)
                        repeatUntilGetBestError step initialError initialBeta (epsilon / 5.0) initialBeta initialQmap initialTaskAggr initialError
                    Just beta' -> do
                        (qmap',taskAggr',err') <- step (Just beta')
                        return (beta', qmap',taskAggr', err')
  return (finalBeta,finalQmap,finaltaskAggr,finalError)

repeatUntilGetBestError :: (Maybe Double -> IO (M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])],Double)) -> Double -> Double -> Double -> Double -> M.Map [String] Double -> M.Map [String] [(String, [(String, (Double, Double))])] -> Double -> IO (Double, M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double)
repeatUntilGetBestError step prevError betaMin betaMax bestBeta bestQmap bestTaskAggr bestError = do
    let nextBeta = (betaMax + betaMin) / 2.0
    (nextQmap, nextTaskAggr, nextError) <- step (Just nextBeta)
    let (bestBeta', bestQmap', bestTaskAggr', bestError') = if nextError < bestError then (nextBeta, nextQmap, nextTaskAggr, nextError) else (bestBeta, bestQmap, bestTaskAggr, bestError)
    if (betaMax - betaMin > 0.01) && (betaMax > 0.01) && (betaMin /= 1/0) && (betaMax /= 1/0)
      then do
        --do binary search
        if (prevError <= nextError) then do
            repeatUntilGetBestError step prevError betaMin nextBeta bestBeta' bestQmap' bestTaskAggr' bestError'
        else do
            repeatUntilGetBestError step nextError nextBeta betaMax bestBeta' bestQmap' bestTaskAggr' bestError'
      else do
        return (bestBeta', bestQmap', bestTaskAggr', bestError')

-- if we have several final groups, we combine errors into an l2-norm of errors
extractFinalResults :: Double -> [(String, [(String, (Double, Double))])] -> [String] -> [((String,String),[([String], Double, Double, Double)])]
extractFinalResults qr taskAggr key =
    concat $ map (\(taskName,res) -> map (\ (tableName, (b,sds)) -> ((taskName,tableName), [(key, qr, b, sds)])) res   ) taskAggr

extractFinalResult :: Double -> [(String, [(String, (Double, Double))])] -> String -> String -> (Double,Double,Double)
extractFinalResult qr taskAggr taskName tableName =

  let resultMap = M.fromList $ (M.fromList taskAggr) ! tableName in
  let (b, sds) = resultMap ! taskName in
  (qr, b, sds)

-- let the sensitivity of a group-by query be the sum of sensitivities of its groups (to show why we increase epsilon), we use it only as a GA analysis output
-- let the error of a group-by query be the l2 norm of all errors
combinedSdss :: [Double] -> Double
combinedSdss sdss = sum sdss

combinedEtas :: [Double] -> [Double] -> [Double]
combinedEtas bs sdss = zipWith (\b sds -> (sds / b)) bs sdss

combinedErrs :: [Double] -> [Double] -> [Double] -> Double
combinedErrs qrs bs sdss = sqrt $ sum $ zipWith3 (\qr b sds -> ((sds / b) / qr) ^ 2) qrs bs sdss


performAnalysisBetaStep :: ProgramOptions -> String -> Double -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> BQ.DataWrtTables -> M.Map String VarState -> [(String, Maybe Double)] -> [Int] -> Maybe Double -> IO (M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double)
performAnalysisBetaStep args outputTableName epsilon dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts beta = do

  (qmap,taskAggrMap) <- performAnalysis args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts
  let (qrs, bs, sdss) = unzip3 $ map (\key -> extractFinalResult (qmap ! key) (taskAggrMap ! key) B.resultForAllTables outputTableName) (M.keys qmap)
  let err = combinedErrs qrs bs sdss

  return (qmap,taskAggrMap,err)


performAnalysis :: ProgramOptions -> Double -> Maybe Double -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> BQ.DataWrtTables -> M.Map String VarState -> [(String, Maybe Double)] -> [Int] -> IO (M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])])
performAnalysis args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

  (qmap,taskAggrMap') <- BQ.performAnalyses args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts

  -- if we choose beta that is not compatible with epsilon during optimization, we get a negative b, so we set it to 0 to get Infinity relative error
  -- in policy analysis, this means that desired epsilon, and hence the guessing advantage bound, could not be achieved
  let taskAggrMap = M.fromList $ map (\(key,taskAggrGroup) -> (key, map (\(taskName,res) -> (taskName, map (\ (tableName, (b,sds)) -> (tableName, (max b 0, sds)) ) res)) taskAggrGroup)) (M.toList taskAggrMap')
  return (qmap, taskAggrMap)

allCombsOfLists [] = [[]]
allCombsOfLists (xs:xss) =
    [(y:ys) | y <- xs, ys <- allCombsOfLists xss]

allCombsOfMaybeLists :: [Maybe [a]] -> [[Maybe a]]
allCombsOfMaybeLists [] = [[]]
allCombsOfMaybeLists (xs:xss) =
    concat [z | ys <- allCombsOfMaybeLists xss, let z = case xs of {Nothing -> [(Nothing : ys)]; _ -> [((Just y) : ys) | y <- (fromJust xs)]}]
