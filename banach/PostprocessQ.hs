{-# LANGUAGE MultiParamTypeClasses#-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}

module PostprocessQ where

import Debug.Trace

import Control.Monad
import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import ProgramOptions
import Text.PrettyPrint.Tabulate
import qualified Text.PrettyPrint.Tabulate as T
import qualified GHC.Generics as G
import Data.Data
import Numeric
import Text.Printf
import ErrorMsg

import qualified Banach as B
import qualified BanachQ as BQ
import DatabaseQ
import PolicyQ
import GroupQ
import AexprQ

traceIOIfDebug :: Bool -> String -> IO ()
traceIOIfDebug debug msg = do
    if debug then traceIO msg
    else return ()


-- this is used only for nice output printing
data Result = Result {sensitivity :: String, query_result :: String,
                      cauchy_abs_err :: String, cauchy_rel_err :: String, cauchy_noise :: String,
                      beta :: String, delta :: String,
                      laplace_abs_err :: String, laplace_rel_err :: String, laplace_noise :: String,
                      norm :: String} deriving (Data, G.Generic, Show)

constructResult [qr, cauchyNoise, cauchyError, cauchyScale, norm, beta, sds, laplaceDelta, laplaceNoise, laplaceError, laplaceScale]
     = Result {sensitivity  = sds,
               query_result = qr,
               cauchy_abs_err = cauchyNoise,
               cauchy_rel_err = cauchyError,
               cauchy_noise = cauchyScale,
               beta = beta,
               delta = laplaceDelta,
               laplace_abs_err = laplaceNoise,
               laplace_rel_err = laplaceError,
               laplace_noise = laplaceScale,
               norm = norm}

constructResult [norm, beta, sds, laplaceDelta]
     = Result {sensitivity  = sds,
               query_result = "--",
               cauchy_abs_err = "--",
               cauchy_rel_err = "--",
               cauchy_noise = "--",
               beta = beta,
               delta = laplaceDelta,
               laplace_abs_err = "--",
               laplace_rel_err = "--",
               laplace_noise = "--",
               norm = norm}

niceListPrint :: Bool -> [Double] -> String
niceListPrint False xs = printFloatS (head xs)
niceListPrint True xs  = "[" ++ intercalate ", " (map printFloatS xs) ++ "]"

printAdditiveTerm x y =
    -- if x is 0, then there is no scaling needed, which means that the continuous approximation is also not needed
    if x == 0 then "0.0"
    else if y == 0 then printFloatS x ++ "*z"
    else if y > 0 then  printFloatS x ++ "*z" ++ "+" ++ printFloatS y
    else                printFloatS x ++ "*z" ++ "-" ++ printFloatS (abs y)

computeAdditiveTerm z x y =
    -- if x is 0, then there is no scaling needed, which means that the continuous approximation is also not needed
    if x == 0 then 0.0
    else if y == 0 then x * z
    else x * z + abs y

niceListScalingPrint :: Bool -> [Double] -> [Double] -> String
niceListScalingPrint False xs ys = printAdditiveTerm (head xs) (head ys)
niceListScalingPrint True  xs ys = let zs = zipWith (\x y -> printAdditiveTerm x y) xs ys in
                                   "[" ++ intercalate ", " zs ++ "]"

--output labels
niceOutput_tableName      = "output table name"

niceOutput_y              = "actual query results y"
niceOutput_err errorUB    = show (round $ errorUB * 100) ++ "%-absolute error |a|"
niceOutput_relErr errorUB = show (round $ errorUB * 100) ++ "%-realtive error |a|/|y|"

niceOutput_cauchyDistr = "Cauchy noise distribution"

niceOutput_delta d              = "DP delta" ++ (if d == "" then "" else " (" ++ d ++ ")")
niceOutput_err_alt d errorUB    = niceOutput_err errorUB ++ "(" ++ d ++ ")"
niceOutput_relErr_alt d errorUB = niceOutput_relErr errorUB ++ "(" ++ d ++ ")"

niceOutput_laplaceDistr   = "Laplace noise distribution"

niceOutput_prior     = "prior (worst instance)"
niceOutput_posterior = "posterior (worst instance)"

niceOutput_norm = "norm N"
niceOutput_beta = "smoothness beta"
niceOutput_sds = "beta-smooth sensitivity w.r.t. N"
niceOutput_eps d = "DP epsilon" ++ (if d == "" then "" else " (" ++ d ++ ")")

-- descriptions of noise probability density functions
nicePDF_Cauchy  = "sqrt(2) / pi * 1 / (1 + |x|^4)"
nicePDF_Laplace = "1 / 2 * exp(-x)"

niceNormPrintFull normExpr normAggr =
    let mainNorm = niceNormPrint normExpr in
    if mainNorm == "" then "--" else niceNormPrint normExpr ++ ", rows l_" ++ niceADoublePrint normAggr


-- number of steps in optimization
numOfSearchSteps = fromIntegral 100

-- nice printing
niceRound x = fromIntegral (round (x * 1000)) / 1000
printFloatL = printf "%0.6f"
printFloatS = printf "%0.2f"
printFloatE = (\x -> showEFloat (Just 2) x "")

-- lambert's W function: finds y such that y * exp(y) = x
lambert x 0 = 1
lambert x n =
    let an = lambert x (n - 1) in
    an - (an * exp(an) - x) / ((an + 1) * exp(an))

-- int sqrt(2) / pi * 1 / (1 + x^4) dx
cauchy_integral a =
    let x1 = - log (a**2 - (sqrt 2) * a + 1) in
    let x2 =   log (a**2 + (sqrt 2) * a + 1) in
    let x3 = - 2 * (atan (1 - (sqrt 2) * a)) in
    let x4 =   2 * (atan (1 + (sqrt 2) * a)) in
    (x1 + x2 + x3 + x4) / (4 * pi)

-- int 1 / 2 * exp(-|x|) dx
laplace_integral a =
    1 / 4 * (exp (-a)) * ((exp a - 1)**2 * (- (signum a)) + 2 * (exp a) + (exp (2 * a)) - 1)

-- find the range within which the noise stays with probability p
-- we use window binary search, as we do not have better ideas
find_noise_range_window f p w =
    let q = (f w) - (f (-w)) in
    if p > q then find_noise_range_window f p (w*2)
    else find_noise_range_binary f p 0 w

find_noise_range_binary f p lb ub =
    let a = (ub + lb) / 2 in
    let q = (f a) - (f (-a)) in
    if abs (q - p) < 0.01 then a
    else if p > q then find_noise_range_binary f p a ub
    else find_noise_range_binary f p lb a

-- given max-distance d, aimed guessing advantage bound ga, and probailities p, q, compute epsilon
compute_epsilon :: Bool -> Double -> Double -> Double -> Double -> Double
compute_epsilon _ _ 1 1 _ = 1/0
compute_epsilon pos ga' q p d =

    -- we know that the probability cannot grow above 100%
    if pos then
        let ga = min (1 - p) ga' in
        let z = p / (q - p) * (1 / (ga + p) - 1) in
        --trace ("eps1: " ++ show p ++ " " ++ show q ++ " " ++ show ga ++ " " ++ show z ++ " " ++ show (- (log z) / d)) $
        - (log z) / d
    else
        let ga = min p ga' in
        let z = (q - p) / p * (q / (ga + (1 - p) - (1 - q)) - 1) in
        --trace ("eps0: " ++ show p ++ " " ++ show q ++ " " ++ show ga ++ " " ++ show z ++ " " ++ show (- (log z) / d)) $
        - (log z) / d

compute_worst_epsilon :: Double -> Double -> Double -> Double
compute_worst_epsilon ga q d =
    (2 / d) * (log ((sqrt q + sqrt (ga*(ga + q - 1))) / (1 - ga)))

-- given a bounding box with side length a, compute the epsilon required to hide a unit box there
compute_eps_for_a :: Bool -> Double -> Int -> M.Map String [Either Double String] -> [(Int, M.Map [String] PlcData)] -> Double -> Int -> (Double,Double,Double,Double)
compute_eps_for_a pos ga numOfRows xmap expr sample_a nq =

    -- compute the weight of X' (distributions of some dimensions can be unknown)
    -- if different elements come with different probabilities, we consider all combinations
    --trace ("xmap: " ++ show xmap) $
    --trace ("expr: " ++ show expr) $
    let qssAs = map (\(s,m) -> let (vss,ass) = unzip $ map (\varNames ->

                                    -- adjust proposed sample_a to the actual bounds R
                                    -- the returned list 'as' is the list of max-distances
                                    let (PlcData b ur r rr d g) = m ! varNames in
                                    let xss = map (xmap !) varNames in

                                    -- non-sensitive dimensions do not change anything
                                    if not b then
                                        unzip $ replicate numOfRows (1.0, 1.0)
                                    else
                                        -- this 'aa' defines distance in the scaled space
                                        -- the value 'aa * ur' should be used to compute g
                                        let aa = if d then rr
                                                else max r $ min rr sample_a
                                        in unzip $ map (\xs -> case g xs (ur * aa) of
                                                          Nothing   -> (1.0, if d then 1.0 else 2.0 * rr)
                                                          -- since g has been computed in non-scaled space, we need to scale 'a' back
                                                          Just (v,a)-> (v, a / ur)) xss
                                    ) (M.keys m)
                               in
                                    (map (((fromIntegral s) * ) . product) (transpose vss), foldr max 1.0 (concat ass))) expr
    in

    let pss'  = map (\(s,m) -> let vss = map (\varNames ->

                                    let (PlcData b ur r _ _ g) = m ! varNames in
                                    let xss = map (xmap !) varNames in

                                    if not b then
                                         Just $ replicate numOfRows 1.0
                                    else
                                         let vs = map (\xs -> case g xs (ur * r) of
                                                          Nothing   -> Nothing
                                                          Just (v,a)-> Just v) xss
                                         in (if elem Nothing vs then Nothing else Just (map fromJust vs))
                                    ) (M.keys m)
                               in
                                    if elem Nothing vss then replicate numOfRows Nothing
                                    else
                                        let wss = transpose $ (map fromJust) vss in
                                        map ((Just . ((fromIntegral s) *) . product) ) wss) expr
    in

    -- determine the unique bound 'a' that is true for all dimensions
    let (qss',as) = unzip qssAs in
    let a = foldr max 1 as in
    let d = a * fromIntegral nq in

    let pss = transpose pss' in
    let qss = transpose qss' in

    --trace (show sample_a)
    --trace ("pss: " ++ show pss) $
    --trace ("qss: " ++ show qss) $

    -- compute the epsilon (use worst-case p if p is unknown)
    let results = zipWith (\ps qs ->
                       let q = sum qs in
                       if elem Nothing ps then
                               let eps = compute_worst_epsilon ga q d in
                               let p = min q ((sqrt q) * ((exp (d * eps / 2)) - (sqrt q)) / ((exp (d * eps)) - 1)) in
                               (a,eps,q,p)
                       else
                               let p = sum (map fromJust ps) in
                               let eps = compute_epsilon pos ga q p d in
                               (a,eps,q,p)
                  ) pss qss
    in

    -- if there are many possible values of p in the given set of sensitive rows, then choose the worst one
    let (a,epsilon,q,p) = foldr (\x1@(_,e1,_,_) x2@(_,e2,_,_) -> if isNaN e2 || e1 < e2 then x1 else x2) (head results) (tail results) in
    (a,epsilon,q,p)


optimal_a_epsilon :: Bool -> Double -> Int -> M.Map String [Either Double String] -> Double -> Double -> [(Int, M.Map [String] PlcData)] -> Double -> Double -> Double -> Double
                     -> Double -> Double -> Int -> (Double,Double,Double,Double)
optimal_a_epsilon _ _ _ _ _ _ _ a epsilon q p 0 _ _ = (a,epsilon,q,p)
optimal_a_epsilon pos ga numOfRows xmap scaled_r scaled_rr expr a epsilon q p k n nq =

    -- compute the sample value for a and check how good it is
    let sample_a = scaled_r + k * (scaled_rr - scaled_r) / n in
    let (a',epsilon',q',p') = compute_eps_for_a pos ga numOfRows xmap expr sample_a nq in

    --take the best values found so far
    let (a'',epsilon'',q'',p'') = if isNaN epsilon || epsilon' > epsilon then (a',epsilon',q',p') else (a,epsilon,q,p) in
    optimal_a_epsilon pos ga numOfRows xmap scaled_r scaled_rr expr a'' epsilon'' q'' p'' (k-1) n nq


performDPAnalysis :: [String] -> [String] -> ProgramOptions -> String -> String -> String -> String -> [String] -> Int -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> AttMap -> [(String, Maybe Double)] -> [Int] -> IO ()
performDPAnalysis tableNames tableAliases args outputTableName dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

  let debug    = not (alternative args)
  let vb       = not (succinct args)
  let epsilon' = getEpsilon args
  let beta     = getBeta args
  let delta    = getDelta args

  -- extend attMap to table aliases
  let tableAliasMap = M.fromListWith (++) $ zip tableNames (map (\x -> [x]) tableAliases)
  let fullAttMap    = M.fromList $ concat $ map (\(varName,varState) ->
                                                    let [tableName,x] = varNameToTableAndSubVarName varName in
                                                    let xs = if M.member tableName tableAliasMap then (tableAliasMap ! tableName) else [] in
                                                    map (\ta -> (preficedVarName ta x, varState)) xs
                                                ) (M.toList attMap)


  -- rescale noise distributions in such a way that the reported error bound holds with confidence errorUB
  let errorUB = errorUBprob args
  let rescaleCauchy  = find_noise_range_window cauchy_integral errorUB 1
  let rescaleLaplace = find_noise_range_window laplace_integral errorUB 1

  -- do not look for optimal beta if it has been specified by the user
  (initQmap,modQmap,taskAggrMap) <- case beta of
          Just _  -> performAnalysis args False epsilon' beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData fullAttMap tableGs colTableCounts
          Nothing -> do
                         (_,initQM,modQM,tm,_) <- findOptimalBeta args rescaleCauchy outputTableName epsilon' beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData fullAttMap tableGs colTableCounts
                         return (initQM,modQM,tm)

  -- if we have a GroupBy query, we need to scale epsilon accordingly
  let epsilon = epsilon' / (fromIntegral numOfOutputs)

  traceIOIfDebug (debug && vb) ("===============================")
  traceIOIfDebug (debug && vb) ("initial qmap: " ++ (show initQmap))
  traceIOIfDebug (debug && vb) ("modified qmap: " ++ (show modQmap))
  traceIOIfDebug (debug && vb) ("final taskAggr: " ++ (show taskAggrMap))

  -- if a group is empty, we set its output to 0
  -- TODO think how to define for MIN/MAX queries in a better way
  let outMap = M.fromListWith (++) $ concat $ map (\key -> extractFinalResults (if M.member key initQmap then initQmap ! key else 0) (if M.member key modQmap then modQmap ! key else 0) (taskAggrMap ! key) key) (M.keys taskAggrMap)
  let outList = map (\((taskName,tableName), zs) -> (taskName,[(tableName,zs)])) $ M.toList outMap
  let taskList' = M.toList $ M.fromListWith (++) outList

  let sep1 = if alternative args && not (succinct args) then [B.unitSeparator] else "\n"
  let sep2 = if alternative args && not (succinct args) then [B.unitSeparator2] else "\n\n"
  let sep3 = if alternative args && not (succinct args) then [B.unitSeparator3] else " "

  let (_,normsExprs,normsAggrs) = unzip3 $ map BQ.getExtra tableExprData
  let inputTableNames = BQ.getTableNames tableExprData
  let normMap = M.fromList $ zip inputTableNames $ zip normsExprs normsAggrs

  traceIOIfDebug debug ("===============================")
  traceIOIfDebug debug ("Use the numbers in the table below to achieve DP as follows:")
  traceIOIfDebug debug ("Cauchy noise distribution:  add noise 'cauchy_scale' with z <- sqrt(2) / pi * 1 / (1 + |x|^4)")
  traceIOIfDebug debug ("Laplace noise distribution: add noise 'laplace_scale' with z <- 1 / 2 * exp(-x)")


  let allTablesNorm = "||.||_1"

  -- result the output table comes first
  let taskList = sortBy (\(a,_) _ -> if a == outputTableName then LT else GT) taskList'

  let taskStr =
          map (\(taskName,res') ->
                  -- result for all tables comes first
                  let res = sortBy (\(a,_) _ -> if a == B.resultForAllTables then LT else GT) res' in
                  (taskName, (map (\ (tableName, zs) ->
                      let (_,initQrs,modQrs,bs,sdss) = unzip5 zs in

                      -- do not print brackets if the list has exactly one element
                      let printList = niceListPrint (length initQrs /= 1) in
                      let printScalingList = niceListScalingPrint (length initQrs /= 1) in

                      let qr  = printList initQrs in

                      let constOffset = noiseOffset initQrs modQrs in

                      let cauchyScaling = noiseScaling bs sdss in

                      -- we use the constOffset to measure the total error (which depens on actual data anyway)
                      let cauchyNoise   = zipWith (computeAdditiveTerm rescaleCauchy) cauchyScaling constOffset in
                      let cauchyError   = relativeError initQrs cauchyNoise in

                      -- we do not use the constOffset in the reported noise distribution since it might be public
                      let publishedConstOffset = replicate (length initQrs) 0.0 in

                      let sds = printList sdss in
                      let norm = if tableName == B.resultForAllTables then

                                      -- if there are two entries in the result, then there is just one table
                                      if length res <= 2 then
                                          let (tableName',_) = head res in
                                          let (normExpr,normAggr) = (normMap ! tableName') in
                                          niceNormPrintFull normExpr normAggr

                                      -- if there are more entries, but all other tables are insensitive
                                      -- we can take the norm of the only sensitive table
                                      else
                                          let allNorms = filter (/= "--") $ map (uncurry niceNormPrintFull) $ M.elems normMap in
                                          if length allNorms == 1 then
                                              head allNorms
                                          -- if there are several sensitive tables, we do not write out the full norm
                                          else
                                              allTablesNorm
                                 else
                                      let (normExpr,normAggr) = (normMap ! tableName) in
                                      niceNormPrintFull normExpr normAggr
                      in

                      -- these betas should all be the same in our implementation, otherwise DP w.r.t. several outputs is not well-defined
                      let allBetas = map (\b -> epsilon / (4 + 1) - b) bs in
                      let finalBeta    = printFloatL $ foldr max 0 allBetas in

                      -- if beta = 0, we get delta = 0 and b = eps - beta
                      let deltaLB = 2*exp(epsilon-1-epsilon / (foldr max 0 allBetas)) in

                      let laplaceDeltas = map (\beta    -> if deltaLB == 0 then 0 else max delta deltaLB) allBetas in
                      let laplaceBs = zipWith (\beta d  -> if deltaLB == 0 then epsilon - beta else log ((d / deltaLB)**beta)) allBetas laplaceDeltas in

                      let laplaceDelta   = printFloatE $ foldr min (1/0) laplaceDeltas in

                      --trace ("laplace bs1: " ++ show laplaceBs) $

                      let laplaceScaling = noiseScaling laplaceBs sdss in
                      let laplaceNoise   = zipWith (computeAdditiveTerm rescaleLaplace) laplaceScaling constOffset in
                      let laplaceError   = relativeError initQrs laplaceNoise in

                      let outputList =
                              [ ((niceOutput_tableName,      id), tableName)
                              ] ++
                              if taskName == outputTableName then
                                  [ ((niceOutput_y,              id), qr)
                                  , ((niceOutput_err errorUB,    id), printList  cauchyNoise)
                                  , ((niceOutput_relErr errorUB, id), printFloatL (cauchyError * 100) ++ "%")
                                  , ((niceOutput_cauchyDistr,    \x -> "add noise " ++ x ++ ", where z ~ " ++ nicePDF_Cauchy), printScalingList cauchyScaling publishedConstOffset)
                                  , ((niceOutput_norm, \x -> if x == allTablesNorm then "an l_1-norm of all input table norms" else norm), norm)
                                  , ((niceOutput_beta, id), finalBeta)
                                  , ((niceOutput_sds,  id), sds)
                                  , ((niceOutput_delta "Laplace",              id), laplaceDelta)
                                  , ((niceOutput_err_alt "Laplace" errorUB,    id), printList  laplaceNoise)
                                  , ((niceOutput_relErr_alt "Laplace" errorUB, id), printFloatL (laplaceError * 100) ++ "%")
                                  , ((niceOutput_laplaceDistr, \x -> "add noise " ++ x ++ ", where z ~ " ++ nicePDF_Laplace), printScalingList laplaceScaling publishedConstOffset)
                                  ]
                             else
                                  [ ((niceOutput_norm, \x -> if x == allTablesNorm then "an l_1-norm of all input table norms" else norm), norm)
                                  , ((niceOutput_beta, id), finalBeta)
                                  , ((niceOutput_sds,  id), sds)
                                  , ((niceOutput_delta "Laplace",              id), laplaceDelta)
                                  ]
                      in

                      outputList) res)

          )) taskList

  -- for interaction with PLEAK, we keep the names of outputs
  when ((alternative args) && not (succinct args)) $ putStrLn $ intercalate sep2 $ map (\(taskName, xss) -> taskName ++ sep1 ++ intercalate sep1 (map (\xs -> intercalate sep3 (tail $ concat $ map (\((x,f),y) -> [x, f y]) xs)) xss)) taskStr

  -- for automated tests, we discard output names (since they are prone to changes) and keep only the values
  when ((alternative args) && (succinct args)) $ putStrLn $ intercalate sep2 $ map (\(taskName, xss) -> taskName ++ sep1 ++ intercalate sep1 (map (\xs -> intercalate sep3 (map snd xs)) xss)) taskStr

  forM taskStr $ \(taskName,tableMap) -> do
          when debug $ putStrLn ("-------------------------\nTask: " ++ taskName)
          let tableResultMap = M.fromList $ map (\(v : vs) -> (snd v, constructResult (map snd vs))) tableMap
          when debug $ T.printTable tableResultMap
  putStr ""


performPolicyAnalysis :: [String] -> [String] -> ProgramOptions -> String -> String -> String -> String -> [String] ->Int -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> PlcCostType -> AttMap -> [Int] -> IO ()
performPolicyAnalysis tableNames tableAliases args outputTableName dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData plcCostType attMap colTableCounts = do

  -- the input epsilon now works as GA, the upper bound on attacker's advantage
  let debug = not (alternative args)
  let vb    = not (succinct args)

  let ga = getEpsilon args
  let fixedBeta = getBeta args

  -- this basically scales epsilon nq times, assuming that up to nq queries may be run on the same data
  -- we actually have numOfOutputs as well, but that will be taken into account by Banach analyser
  let nq = numOfQueries args

  -- extend attMap to table aliases
  let tableAliasMap = M.fromListWith (++) $ zip tableNames (map (\x -> [x]) tableAliases)
  let fullAttMap    = M.fromList $ concat $ map (\(varName,varState) ->
                                                    let [tableName,x] = varNameToTableAndSubVarName varName in
                                                    let xs = if M.member tableName tableAliasMap then (tableAliasMap ! tableName) else [] in
                                                    map (\ta -> (preficedVarName ta x, varState)) xs
                                                ) (M.toList attMap)

  -- extract the sensitive expression and the variables used within it
  let plcExpr = getStatement plcCostType
  let allSensVars = extract_vars plcExpr
  let sensVarList = nub $ concat allSensVars

  -- construct the query that reads sensitive data from source tables
  let plcFilterMap = M.fromList $ getFilters plcCostType
  let sensTableNames = M.keys plcFilterMap

  let selStr   = intercalate ", " sensVarList
  let fromStr  = intercalate ", " sensTableNames
  let whereStr = intercalate " AND " $ map (\tn -> let prefix = tn ++ [tsep] in
                                                   aexprToString $ updatePreficesAexpr (S.fromList sensTableNames) prefix (plcFilterMap ! tn)
                                            ) (M.keys plcFilterMap)
  let dataQuery = "SELECT " ++ selStr ++ " FROM " ++ fromStr ++ " WHERE " ++ whereStr ++ ";"

  -- process the policy and the attacker knowledge
  let plainTypeMaps = map (\(tname,tmap) -> map (\(x,y) -> (preficedVarName tname x,y)) tmap) typeMap
  let plainTypeMap  = M.fromList $ concat plainTypeMaps

  -- extract the actual data (we will need it to compute priors)
  results <- sendQueryToDb args dataQuery
  let numOfRows = length results
  let xmap = M.fromList $ zipWith (\var rs -> if plainTypeMap ! var == "text" then
                                                  (var, map (Right . sqlToString) rs)
                                              else
                                                  (var, map (Left . sqlToDouble) rs) ) sensVarList (transpose results)

  traceIOIfDebug (debug && vb) ("type map: " ++ show plainTypeMap)
  traceIOIfDebug (debug && vb) ("data query: " ++ show dataQuery)
  --traceIOIfDebug (debug && vb) ("xmap: " ++ show xmap)

  -- compute parameters of the sensitivie attributes
  let unit_r_map =  traverseExpr (M.unionWith min) (M.unionWith min) (const M.empty) (\(var,plcState) ->
                                   let r  = extract_r plcState in
                                   M.singleton var r) plcExpr

  let plcExprExt = rewriteExpr (\(var,plcState) ->
                                     let b  = extract_b attMap plcState var in
                                     let r  = extract_r plcState in
                                     let rr = extract_R attMap plainTypeMap plcState var in
                                     let d  = extract_d plcState in
                                     let g  = extract_g attMap var in
                                     let unit_r = unit_r_map ! var in
                                     (var, PlcData b unit_r (r / unit_r) (rr / unit_r) d g)) plcExpr

  -- further, we assume r = 1 everywhere in each dimension
  let scaled_r  = 1
  let scaled_rr = traverseExpr max max (const 0) (\(var,plcState) -> let r  = extract_r plcState in
                                                                     let rr = extract_R attMap plainTypeMap plcState var in
                                                                     rr / r) plcExpr

  -- this norm is used only to show it in the output
  let norm = deriveDbNorm attMap plcExpr


  -- compute p and q using the equalities and P(A || B) = P(A) + P(B) - P(AB), P(AA) = P(A), P(AB) = P(A)*P(B)
  let pqExpr = computePweights plcExprExt

  -- it seems that brute-forcing optimal epsilon and a works quite well
  -- we consider multidimensional space, where the radius is linf-norm
  let num_of_tries = 10000

  -- since 'a' is only an estimation parameter, we find the noise separately for the positive and the negative guess, and then take the largest noise
  let (init_a, init_epsilon, init_q, init_p) = compute_eps_for_a True ga numOfRows xmap pqExpr scaled_rr nq
  let (a1,epsilon1,q1,p1) = if ga == 0 then (init_a, init_epsilon, init_q, init_p) else optimal_a_epsilon True ga numOfRows xmap scaled_r scaled_rr pqExpr init_a init_epsilon init_q init_p numOfSearchSteps numOfSearchSteps nq

  let (init_a, init_epsilon, init_q, init_p) = compute_eps_for_a False ga numOfRows xmap pqExpr scaled_rr nq
  let (a0,epsilon0,q0,p0) = if ga == 0 then (init_a, init_epsilon, init_q, init_p) else optimal_a_epsilon False ga numOfRows xmap scaled_r scaled_rr pqExpr init_a init_epsilon init_q init_p numOfSearchSteps numOfSearchSteps nq

  let (a,epsilon',q,p) = if epsilon0 < epsilon1 then (a0,epsilon0,1-q0,1-p0) else (a1,epsilon1,q1,p1)

  traceIOIfDebug (debug && vb) ("plcExpr: " ++ show plcExpr)
  traceIOIfDebug (debug && vb) ("plcExprExt: " ++ show plcExprExt)
  traceIOIfDebug (debug && vb) ("pqExpr: " ++ show pqExpr)
  traceIOIfDebug (debug && vb) ("allSensVars: " ++ show allSensVars)
  traceIOIfDebug (debug && vb) ("--------")
  traceIOIfDebug (debug && vb) ("GA: " ++ (show ga))
  traceIOIfDebug (debug && vb) ("--------")
  traceIOIfDebug (debug && vb) ("scaled rr: " ++ (show scaled_rr))
  traceIOIfDebug (debug && vb) ("scaled r: " ++ (show scaled_r))
  traceIOIfDebug (debug && vb) ("--------")
  traceIOIfDebug (debug && vb) ("a0: " ++ (show a0))
  traceIOIfDebug (debug && vb) ("eps0: " ++ (show epsilon0))
  traceIOIfDebug (debug && vb) ("q0: " ++ (show q0))
  traceIOIfDebug (debug && vb) ("p0: " ++ (show p0))
  traceIOIfDebug (debug && vb) ("--------")
  traceIOIfDebug (debug && vb) ("a1: " ++ (show a1))
  traceIOIfDebug (debug && vb) ("eps1: " ++ (show epsilon1))
  traceIOIfDebug (debug && vb) ("q1: " ++ (show q1))
  traceIOIfDebug (debug && vb) ("p1: " ++ (show p1))

  --error "STOP"
  let pr_pre  = p1 * 100
  let pr_post = 1 / (1 + exp(- a1 * epsilon1 * (fromIntegral nq)) * (q1-p1) / p1) * 100

  -- the following output is more informative, but less understandable
  -- if ga < prior, then the lower bound may be negative, and we take the bound 0 in this case
  --let pr_post = [max 0 (q0 - 1 / (1 + exp(- a0 * epsilon0 * (fromIntegral nq)) * p0 / (q0-p0))) * 100, 1 / (1 + exp(- a1 * epsilon1 * (fromIntegral nq)) * (q1-p1) / p1) * 100]

  -- rescale noise distributions in such a way that the reported error bound holds with confidence errorUB
  let errorUB = errorUBprob args
  let rescaleCauchy  = find_noise_range_window cauchy_integral errorUB 1
  let rescaleLaplace = find_noise_range_window laplace_integral errorUB 1

  (finalBeta,initQmap,modQmap,taskAggrMap,_) <- findOptimalBeta args rescaleCauchy outputTableName epsilon' fixedBeta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData fullAttMap [] colTableCounts

  traceIOIfDebug (debug && vb) ("===============================")
  traceIOIfDebug (debug && vb) ("initial qmap: " ++ (show initQmap))
  traceIOIfDebug (debug && vb) ("modified qmap: " ++ (show modQmap))
  traceIOIfDebug (debug && vb) ("final taskAggr: " ++ (show taskAggrMap))

  -- if we have a GroupBy query, we need to scale epsilon accordingly
  -- we already took into account numOfQueries, now we also need to include numOfOutputs
  -- TODO check why we redefined numOfOutputs earlier, as done in the next line
  -- let numOfOutputs = fromIntegral $ length finalQrs
  let epsilon = epsilon' / (fromIntegral numOfOutputs)

  --let expectedCost = ga * cost
  traceIOIfDebug debug ("Cauchy params: beta=" ++ (show finalBeta) ++ ", eps=" ++ (show epsilon))

  -- additional outputs
  let (initQrs, modQrs, cauchyBs, finalSdss) = unzip4 $ map (\key -> extractFinalResult (if M.member key initQmap then initQmap ! key else 0) (if M.member key modQmap then modQmap ! key else 0) (taskAggrMap ! key) B.resultForAllTables outputTableName) (M.keys taskAggrMap)

  let constOffset   = noiseOffset initQrs modQrs
  let publishedConstOffset = replicate (length initQrs) 0.0

  let cauchyScaling = noiseScaling cauchyBs finalSdss
  let cauchyNoise   = zipWith (computeAdditiveTerm rescaleCauchy) cauchyScaling constOffset
  let cauchyError   = relativeError initQrs cauchyNoise

  -- (epsilon,delta)-DP related stuff:

  -- we restore the betas that have been computed before (these betas are not cauchy-specific)
  -- if beta = 0, we get delta = 0
  let allBetas = map (\b -> epsilon / (4 + 1) - b) cauchyBs

  -- this is a too rough estimate, let us do it in another way
  -- let (laplaceEpsilons, laplaceBs) = unzip $ zipWith (if epsilon < 1/0 then findOptimalLapParams epsilon else const $ const (1/0,1/0)) finalSdss allBetas

  let laplaceBs       = map (\beta -> epsilon / (exp (beta * a))) allBetas
  let laplaceEpsilons = zipWith (+) laplaceBs allBetas

  let laplaceDeltas   = zipWith3 (\beta b eps -> if beta == 0 then 0 else 2*exp(eps-1-(eps-b)/beta)) allBetas laplaceBs laplaceEpsilons

  let laplaceScaling = noiseScaling laplaceBs finalSdss
  let laplaceNoise   = zipWith (computeAdditiveTerm rescaleLaplace) laplaceScaling constOffset
  let laplaceError   = relativeError initQrs laplaceNoise

  -- if there are different (eps,delta) for several outputs, we show the minimal of them to the user for short representation
  let laplaceDelta   = foldr min (1/0) laplaceDeltas
  let laplaceEpsilon = foldr min (1/0) laplaceEpsilons

  traceIOIfDebug (debug && vb) ("a: " ++ show a)
  traceIOIfDebug (debug && vb) ("betas: " ++ show allBetas)
  traceIOIfDebug (debug && vb) ("Cauchy bs: " ++ show cauchyBs)
  traceIOIfDebug (debug && vb) ("laplace bs: " ++ show laplaceBs)
  traceIOIfDebug (debug && vb) ("laplace deltas: " ++ show laplaceDeltas)
  traceIOIfDebug (debug && vb) ("laplace epsilons: " ++ show laplaceEpsilons)
  --traceIOIfDebug (debug && vb) ("laplace alphas: " ++ show (map (\eps -> epsilon - eps) laplaceEpsilons))
  traceIOIfDebug (debug && vb) ("Cauchy epsilon: " ++ show epsilon)
  --traceIOIfDebug (debug && vb) ("(1 - delta/chi): " ++ show (zipWith3 (\delta sds b -> 1.0 - 2 * sds * delta / b) laplaceDeltas finalSdss laplaceBs))


  traceIOIfDebug debug ("cauchy rescaling: " ++ show rescaleCauchy)
  traceIOIfDebug debug ("laplace rescaling: " ++ show rescaleLaplace)

  -- analyser output
  traceIOIfDebug debug ("===============================")

  -- do not print brackets if the list has exactly one element
  let printList = niceListPrint (length initQrs /= 1)
  let printScalingList = niceListScalingPrint (length initQrs /= 1)

  let outputList = [(niceOutput_y,              printList initQrs),

                    (niceOutput_err errorUB,    printList   cauchyNoise),
                    (niceOutput_relErr errorUB, printFloatL (cauchyError * 100) ++ "%"),
                    (niceOutput_cauchyDistr,    "add noise " ++ printScalingList cauchyScaling publishedConstOffset ++ ", where z ~ " ++ nicePDF_Cauchy),


                    (niceOutput_prior,     show (niceRound pr_pre) ++ "%"),
                    (niceOutput_posterior, show (niceRound pr_post) ++ "%"),

                    (niceOutput_err_alt "Laplace" errorUB,    printList   laplaceNoise),
                    (niceOutput_relErr_alt "Laplace" errorUB, printFloatL (laplaceError * 100) ++ "%"),
                    (niceOutput_laplaceDistr,                 "add noise " ++ printScalingList laplaceScaling publishedConstOffset ++ ", where z ~ " ++ nicePDF_Laplace),

                    (niceOutput_norm,    niceNormPrint norm),
                    (niceOutput_beta,    show (niceRound finalBeta)),
                    (niceOutput_sds,     printList finalSdss),
                    (niceOutput_eps "",  show (niceRound epsilon))]
                    -- to avoid confusion, let us output delta only if it is not 0.0
                    -- then we do not need to explain our special Laplace mechanism if the standard Laplace works
                    ++ (if laplaceDelta == 0.0 then []
                        else [(niceOutput_eps   "Laplace", show (niceRound laplaceEpsilon)),
                              (niceOutput_delta "Laplace", show (niceRound laplaceDelta))])

  let sep = if alternative args && not (succinct args) then [B.unitSeparator2] else "\n"
  let out = if alternative args then map (\(x,y) -> x ++ sep ++ y) outputList else map (\(x,y) -> x ++ ": " ++ y) outputList
  --let sep = if False then [B.unitSeparator2] else "\n"
  --let out = if False then map snd outputList else map (\(x,y) -> x ++ y) outputList
  putStrLn $ intercalate sep out


findOptimalBeta :: ProgramOptions -> Double -> String -> Double -> Maybe Double -> String -> String -> String -> [String] -> Int -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> AttMap -> [(String, Maybe Double)] -> [Int] -> IO (Double, M.Map [String] Double, M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double)
findOptimalBeta args rescaleCauchy outputTableName epsilon fixedBeta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

    -- define the function that we will optimize
    let step = performAnalysisBetaStep args rescaleCauchy outputTableName epsilon dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts

    -- take fixedBeta if it is defined, and optimize otherwise
    case fixedBeta of
                    Nothing -> do
                        initialBeta' <- BQ.findMinimumBeta args False epsilon Nothing dataPath separator initialQuery colNames typeMap sensitiveVarList tableExprData attMap tableGs colTableCounts
                        -- we cannot use beta=0 for combined sensitivity, as it would result in an infinite loop
                        let betaMax = epsilon / 5.0
                        let betaMin = 0
                        let unit = betaMax / numOfSearchSteps
                        let initialBeta = if combinedSens args && initialBeta' == 0 then unit else initialBeta'
                        (initQmap,modQmap,taskAggr,err) <- step False (Just initialBeta)
                        (optBeta, optQmap, optTaskAggr, optError) <- findOptimalBeta2 unit step betaMin betaMax initialBeta modQmap taskAggr err
                        return (optBeta, initQmap, optQmap, optTaskAggr, optError)
                    Just beta' -> do
                        (initQmap,modQmap,taskAggr,err) <- step False (Just beta')
                        return (beta',initQmap,modQmap,taskAggr,err)

-- binary search on beta
findOptimalBeta2 :: Double -> (Bool -> Maybe Double -> IO (M.Map [String] Double, M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])],Double)) -> Double -> Double -> Double -> M.Map [String] Double -> M.Map [String] [(String, [(String, (Double, Double))])] -> Double -> IO (Double, M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double)
findOptimalBeta2 unit step betaMin betaMax bestBeta bestQmap bestTaskAggr bestError =

    if abs(betaMax - betaMin) <= unit || (betaMax == 1/0) then do
        return (bestBeta, bestQmap, bestTaskAggr, bestError)
    else do
        let betaU = (betaMin + betaMax + unit) / 2.0
        let betaL = (betaMin + betaMax - unit) / 2.0
        (_, qmapU, taskAggrU, errU) <- step True (Just betaU)
        (_, qmapL, taskAggrL, errL) <- step True (Just betaL)
        let (beta, qmap, taskAggr, err, betaMin',betaMax') = if errU < errL then (betaU, qmapU, taskAggrU, errU, betaU, betaMax) else (betaL, qmapL, taskAggrL, errL, betaMin, betaL)
        let (beta', qmap', taskAggr', err') = if err < bestError then (beta, qmap, taskAggr, err) else (bestBeta, bestQmap, bestTaskAggr, bestError)
        findOptimalBeta2 unit step betaMin' betaMax' beta' qmap' taskAggr' err'


-- linear search on beta (experimental, currently not used)
-- remember that we need to start from beta > 0 in CS analysis
findOptimalBetaL :: (Bool -> Maybe Double -> IO (M.Map [String] Double, M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])],Double)) -> Double -> Double -> Double -> M.Map [String] Double -> M.Map [String] [(String, [(String, (Double, Double))])] -> Double -> IO (Double, M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double)
findOptimalBetaL step beta betaMax bestBeta bestQmap bestTaskAggr bestError =

    if (beta > betaMax) || (betaMax == 1/0) then do
        return (bestBeta, bestQmap, bestTaskAggr, bestError)
    else do
        (_, qmap, taskAggr, err) <- step True (Just beta)
        let (beta', qmap', taskAggr', err') = if err < bestError then (beta, qmap, taskAggr, err) else (bestBeta, bestQmap, bestTaskAggr, bestError)
        findOptimalBetaL step (beta+(betaMax / numOfSearchSteps)) betaMax beta' qmap' taskAggr' err'


-- if we have several final groups, we combine errors into an l2-norm of errors
extractFinalResults :: Double -> Double -> [(String, [(String, (Double, Double))])] -> [String] -> [((String,String),[([String], Double, Double, Double, Double)])]
extractFinalResults initQr modQr taskAggr key =
    concat $ map (\(taskName,res) -> map (\ (tableName, (b,sds)) -> ((taskName,tableName), [(key, initQr, modQr, b, sds)])) res   ) taskAggr

extractFinalResult :: Double -> Double -> [(String, [(String, (Double, Double))])] -> String -> String -> (Double,Double,Double,Double)
extractFinalResult initQr modQr taskAggr taskName tableName =

  let resultMap = M.fromList $ (M.fromList taskAggr) ! tableName in
  let (b, sds) = resultMap ! taskName in
  (initQr, modQr, b, sds)

-- the noise distribution scalings
noiseScaling :: [Double] -> [Double] -> [Double]
noiseScaling bs sdss = zipWith (/) sdss bs

-- the constant noise offsets
noiseOffset :: [Double] -> [Double] -> [Double]
noiseOffset initQrs modQrs = zipWith (-) modQrs initQrs

-- the relative error (as a single number)
relativeError :: [Double] -> [Double] -> Double
relativeError qrs errs =
    let qnorm   = sqrt $ sum $ map (^2) qrs  in
    let errnorm = sqrt $ sum $ map (^2) errs in
    errnorm / qnorm

performAnalysisBetaStep :: ProgramOptions -> Double -> String -> Double -> String -> String -> String -> [String] -> Int -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> AttMap -> [(String, Maybe Double)] -> [Int] -> Bool -> Maybe Double -> IO (M.Map [String] Double, M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])], Double)
performAnalysisBetaStep args rescaleCauchy outputTableName epsilon dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts silent beta = do

  (initQmap, modQmap, taskAggrMap) <- performAnalysis args silent epsilon beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts
  let (initQrs, modQrs, bs, sdss) = unzip4 $ map (\key -> extractFinalResult (initQmap ! key) (modQmap ! key) (taskAggrMap ! key) B.resultForAllTables outputTableName) (M.keys initQmap)

  -- we assume that the optimal beta is the one that minimizes Cauchy error w.r.t. given error confidence
  let constOffset   = noiseOffset initQrs modQrs
  let cauchyScaling = noiseScaling bs sdss
  let cauchyNoise   = zipWith (computeAdditiveTerm rescaleCauchy) cauchyScaling constOffset
  let cauchyError   = relativeError initQrs cauchyNoise

  return (initQmap, modQmap, taskAggrMap, cauchyError)


performAnalysis :: ProgramOptions -> Bool -> Double -> Maybe Double -> String -> String -> String -> [String] -> Int -> [String] -> [(String,[(String, String)])] -> BQ.TaskMap -> [String] -> [BQ.DataWrtTable] -> AttMap -> [(String, Maybe Double)] -> [Int] -> IO (M.Map [String] Double, M.Map [String] Double, M.Map [String] [(String, [(String, (Double, Double))])])
performAnalysis args silent epsilon beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts = do

  (initQmap,taskAggrMap',modQmap) <- BQ.performAnalyses' args silent epsilon beta dataPath separator initialQuery initQueries numOfOutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts Nothing

  -- if we choose beta that is not compatible with epsilon during optimization, we get a negative b, so we set it to 0 to get Infinity relative error
  -- in policy analysis, this means that desired epsilon, and hence the guessing advantage bound, could not be achieved
  let taskAggrMap = M.fromList $ map (\(key,taskAggrGroup) -> (key, map (\(taskName,res) -> (taskName, map (\ (tableName, (b,sds)) -> (tableName, (max b 0, sds)) ) res)) taskAggrGroup)) (M.toList taskAggrMap')
  return (initQmap, modQmap, taskAggrMap)

-- ======================================================
-- TODO the following functions are deprecated

-- brute force search over epsilon and b
findOptimalLapParams :: Double -> Double -> Double -> (Double,Double)
findOptimalLapParams pureDPEps sds beta =
    findOptimalEps 0 0 0
    where

        -- in the first loop, we optimize epsilon
        findOptimalEps :: Double -> Double -> Double -> (Double,Double)
        findOptimalEps alpha bestEps bestB =

           if  (alpha > pureDPEps) then (bestEps, bestB) else
           let eps = pureDPEps - alpha in
           let b = findOptimalB eps alpha 0 0 in
           -- the smaller is b, the more noise need to be added (for a fixed sds)
           let (eps',b') = if (b > bestB) && (b + beta <= eps) then (eps, b) else (bestEps, bestB) in
           findOptimalEps (alpha+(pureDPEps / numOfSearchSteps)) eps' b'

        -- in the second loop, we optimize b for the fixed epsilon
        findOptimalB :: Double -> Double -> Double -> Double -> Double
        findOptimalB eps alpha b bestB =
            if  (b > eps - beta) then bestB else
            let z  = 4 * sds * exp(eps-1-((eps-b)/beta)) / b in
            let b' = if (z >= 0) && (z <= 1 - exp(-alpha)) then b else bestB in
            findOptimalB eps alpha (b+((eps - beta) / numOfSearchSteps)) b'

allCombsOfLists [] = [[]]
allCombsOfLists (xs:xss) =
    [(y:ys) | y <- xs, ys <- allCombsOfLists xss]

allCombsOfMaybeLists :: [Maybe [a]] -> [[Maybe a]]
allCombsOfMaybeLists [] = [[]]
allCombsOfMaybeLists (xs:xss) =
    concat [z | ys <- allCombsOfMaybeLists xss, let z = case xs of {Nothing -> [(Nothing : ys)]; _ -> [((Just y) : ys) | y <- (fromJust xs)]}]
