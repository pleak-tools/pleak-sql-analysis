module PolicyQ where

import Control.Monad (void)
import Data.Bits
import Data.Either
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Void
import Debug.Trace

import ErrorMsg
import ExprQ
import GroupQ
import QueryQ
import NormsQ

-------------------------------
---- policy data structures ----
-------------------------------

data VarState
  = Exact | None | Approx Double | Total Int | IntSubSet [Int] | SubSet [String] | Range Double Double | ApproxPrior Double Double
  deriving (Show)

reservedSensRowsKeyword = "sensRows"

-- the cases in which the given attacker guesses the variable with required precision
isLeakedVar :: VarState -> VarState -> Bool
isLeakedVar attState plcState =
    case (attState, plcState) of
            (Exact,_)                -> True
            (Approx r1, Approx r2)   -> r1 <= r2
            (ApproxPrior _ r1, Approx r2) -> r1 <= r2
            (Total  n1, Total  n2)   -> n1 <= n2
            (SubSet xs1, SubSet xs2) -> not $ S.isSubsetOf (S.fromList xs2) (S.fromList xs1)
            (IntSubSet xs1, IntSubSet xs2) -> not $ S.isSubsetOf (S.fromList xs2) (S.fromList xs1)
            -- here we assume that the actual data belongs to (lb,ub) -- i.e. the attacker knowledge is correct
            -- while (ub - lb) / 2 <= r2 would already be sufficient in the case when the actual data is in the middle,
            -- we only claim immediate leakage if it leaks for sure
            (Range lb ub, Approx r2) -> (ub - lb) <= r2
            _                        -> False


-- the variable is not sensitive either if attacker already knows it, or we do not care about it
isSensVar :: VarState -> VarState -> Bool
isSensVar attState plcState =
    if isLeakedVar attState plcState then False
    else case (attState, plcState) of
            (_, None) -> False
            _         -> True

verifyVarSecrecy :: M.Map String VarState -> M.Map String VarState -> String -> (String, (Int, [Bool],[VarName],[Expr]))
verifyVarSecrecy attMap plcMap preficedVar =

    let [prefix,var] = case (varNameToTableAndSubVarName preficedVar) of
                           [s1,s2] -> [s1,s2]
                           _       -> error $ error_badPolicyFormat preficedVar
    in
    if var == reservedSensRowsKeyword then (prefix, (0,[],[],[])) else
    let plcState = plcMap ! preficedVar in
    let attState = if M.member preficedVar attMap then attMap ! preficedVar else None in

    let leakedVar = [isLeakedVar attState plcState] in
    let sensVar = if isSensVar attState plcState then [var] else [] in

    -- constuct the norm, which is NormZero for insensitive vars, L0 for exact guesses, and is abs.value for approximated guesses
    let normVar = case (attState, plcState) of
            (Exact,_)    -> []
            (_, None)    -> []
            (_,Exact)    -> [LZero var]
            (_,Approx r) -> [ScaleNorm (1/r) var]
            (_,Total _)  -> [LZero var]
            (_,SubSet _) -> [LZero var]
            (_,IntSubSet _) -> [LZero var] -- if integers come as a set, we consider l0-norm
            _ -> error $ error_badAttackerPolicyCombination attState plcState
    in

    (prefix, (1, leakedVar,sensVar,normVar))

-- check whether sensitivity w.r.t. that variable needs to be analysed at all
extract_bs :: M.Map String VarState -> M.Map String VarState -> [Bool]
extract_bs attMap plcMap =
    map (extract_b attMap plcMap) (M.keys plcMap)

extract_b :: M.Map String VarState -> M.Map String VarState -> String -> Bool
extract_b attMap plcMap var =
    let plcState = plcMap ! var in
    let attState = if M.member var attMap then attMap ! var else None in
    isSensVar attState plcState

-- extract the guessing radius
extract_rs :: M.Map String VarState -> M.Map String VarState -> [Double]
extract_rs attMap plcMap =
    map (extract_r attMap plcMap) (M.keys plcMap)

extract_r :: M.Map String VarState -> M.Map String VarState -> String -> Double
extract_r attMap plcMap var =
    let plcState = plcMap ! var in
    let attState = if M.member var attMap then attMap ! var else None in
    case (attState, plcState) of
            (_,Exact)    -> 1.0 -- compatible with L0-norm
            (_,Approx r) -> r
            (_,Total _)  -> 1.0 -- this is used only for discrete variables, compatible with L0-norm
            (_,SubSet _) -> 1.0 -- this is used only for discrete variables, compatible with L0-norm
            (_,IntSubSet _) -> 1.0 -- this is used only for discrete variables, compatible with L0-norm
            _ -> error $ error_badAttackerPolicyCombination attState plcState

-- extract whether the dimension has discrete norm
extract_ds :: M.Map String VarState -> M.Map String VarState -> [Bool]
extract_ds attMap plcMap =
    map (extract_d attMap plcMap) (M.keys plcMap)

extract_d :: M.Map String VarState -> M.Map String VarState -> String -> Bool
extract_d attMap plcMap var =
    let plcState = plcMap ! var in
    let attState = if M.member var attMap then attMap ! var else None in
    case (attState, plcState) of
            (_,Exact)    -> True
            (_,Approx r) -> False
            (_,Total _)  -> True
            (_,SubSet _) -> True
            (_,IntSubSet _) -> True
            _ -> error $ error_badAttackerPolicyCombination attState plcState


-- TODO extract the total weight of the space (will make use of ApproxPrior)

-- extract the function computing probabilities in total space
extract_gs :: M.Map String VarState -> M.Map String VarState -> [Double -> Maybe [Double]]
extract_gs attMap plcMap =
    map (extract_g attMap plcMap) (M.keys plcMap)

extract_g :: M.Map String VarState -> M.Map String VarState -> String -> (Double -> Maybe [Double])
extract_g attMap plcMap var =
    let plcState = plcMap ! var in
    let attState = if M.member var attMap then attMap ! var else None in
    case (attState, plcState) of
            (Exact,_)        -> const $ Just [1.0]     -- the sensitive region already has sensitivity 1
            (None, _)        -> const Nothing        -- no knowledge
            -- currently, we assume unform distribution for discrete data
            (Total n, _)    -> (\x -> Just [x / fromIntegral n])
            (SubSet xs,_)    -> let n = length xs in (\x -> Just [x / fromIntegral n])
            (IntSubSet xs,_) -> let n = length xs in (\x -> Just [x / fromIntegral n])
            -- currently, we assume unform distribution for real numbers
            (Range lb ub,_)  -> let rr = (ub - lb) / 2.0 in (\x -> Just [x / rr])
            -- this is for the case when the attacker provides certain r himself
            (ApproxPrior p r, _) -> (\x -> if x == r then Just [p] else Nothing)

            _ -> error $ error_badAttackerPolicyCombination attState plcState

-- extract the total space radius
extract_Rs :: M.Map String VarState -> M.Map String String -> M.Map String VarState -> [Double]
extract_Rs attMap typeMap plcMap =
    map (extract_R attMap plcMap typeMap) (M.keys plcMap)

extract_R :: M.Map String VarState -> M.Map String VarState -> M.Map String String -> String -> Double
extract_R attMap plcMap typeMap var =
    let plcState = plcMap ! var in
    --trace (show attMap) $
    --trace (show plcMap) $
    --trace (show typeMap) $
    --trace "---------" $
    let attState = if M.member var attMap then attMap ! var else None in
    case (attState, plcState) of
            (Exact,_)       -> 1.0 -- compatible with L0-norm
            (None, _)       -> let dataType = typeMap ! var in
                                   case dataType of
                                       "int8"   -> 2^64
                                       "bool"   -> 2.0
                                       _       -> error $ error_unboundedDataType dataType

            (Total n, _)     -> fromIntegral $ n
            (SubSet xs,_)    -> fromIntegral $ length xs
            (IntSubSet xs,_) -> fromIntegral $ length xs
            (Range lb ub,_)  -> (ub - lb) / 2.0
            -- TODO this currently gives correct results, but could be nicer with ub and lb
            (ApproxPrior _ r1, _) -> r1
            _ -> error $ error_badAttackerPolicyCombination attState plcState


-- TODO since we scale all repeating variables in the same way, we may take any of them (let it be the first one)
combineSets :: M.Map String Expr -> M.Map String Expr -> M.Map String Expr
combineSets m1 m2 = 
    M.unionWith const m1 m2

normsFromCombinedData :: M.Map TableName (M.Map String Expr) -> TableName -> [Int] -> (([Int], [VarName]), NormFunction, Maybe Double)
normsFromCombinedData combinedDataMap tableName tableSensRows =
    let varMap = combinedDataMap ! tableName in
    let sensVars = M.keys varMap in
    let normVars = M.elems varMap in
    let normVarNames = (map (\x -> defaultNormVariable ++ show x) [0..(length normVars - 1)]) in
    let tempVarMap = M.fromList $ zip normVarNames normVars in
    let nf = NF (M.insert defaultNormVariable (LInf normVarNames) tempVarMap) (SelectL 1.0 defaultNormVariable) in
    -- if there are no explicit records for sensitive rows, we consider all of them sensitive by deafult
    let recordedTableSensRows = if length tableSensRows == 0 then [0..] else tableSensRows in
    ((recordedTableSensRows,sensVars),nf, Nothing)

constructNormData :: [TableName] -> M.Map String VarState -> [(M.Map String VarState, Double)] -> [(([Int], [VarName]), NormFunction, Maybe Double)]
constructNormData tableNames attMap plcMaps =
    -- we put together all variables of all sensitive sets to define one norm over all of them
    -- TODO we currently assume that, if a variable occurs in several sets, it still has the same sensitivity radius
    let temp = map (constructNormDataSet tableNames attMap . fst) plcMaps in
    let combinedDataMap = foldr (M.unionWith combineSets) M.empty temp in

    --extract the special variables for row sensitivity
    let kwlen = length reservedSensRowsKeyword in
    let tableSensRows = map (extractRange plcMaps) tableNames in

    zipWith (normsFromCombinedData combinedDataMap) tableNames tableSensRows

extractRange plcMaps tableName =
    let key = preficedVarName tableName reservedSensRowsKeyword in
    S.toList $ extractRanges S.empty key (map fst plcMaps)

extractRanges indexSet _ [] = indexSet
extractRanges indexSet key (plcMap:ps) =
    if M.member key plcMap then
        let varState = plcMap ! key in
        let newRange = case varState of
                Range lb ub  -> S.fromList [round lb .. round (ub-1)]
                IntSubSet xs -> S.fromList xs
                _            -> error $ error_badPolicySensRows varState
        in extractRanges (S.union indexSet newRange) key ps
    else
        extractRanges indexSet key ps

constructNormDataSet :: [TableName] -> M.Map String VarState -> M.Map String VarState -> M.Map TableName (M.Map String Expr)
constructNormDataSet tableNames attMap plcMap =
    let vars = M.keys plcMap in
    -- aggregate the variables for each table separately
    let dataMap = M.fromListWith (\(n1,x1s,y1s,z1s) (n2,x2s,y2s,z2s) -> (n1 + n2, x1s ++ x2s, y1s ++ y2s, z1s ++ z2s)) $ map (verifyVarSecrecy attMap plcMap) vars in
    --trace (show dataMap) $
    let (res0,res) = unzip $ map (constructTableNormData dataMap) tableNames in
    let (allNumOfVars, allLeakedVars) = unzip res0 in

    let numOfVars  = sum allNumOfVars in
    let leakedVars = concat allLeakedVars in

    -- find out which variables in the policy are already guessed by the attacker
    let badAttacker = foldr (&&) True leakedVars in
    if (numOfVars > 0 && badAttacker) then error $ error_attackerBreaksEverything else M.fromList res

-- the attacker badness should be checked for all tables together, not one by one
constructTableNormData :: M.Map String (Int, [Bool],[String],[Expr]) -> String -> ((Int, [Bool]), (TableName, M.Map String Expr))
constructTableNormData dataMap tableName =

    if M.member tableName dataMap then
        let (numOfVars, leakedVars, sensVars, normVars) = dataMap ! tableName in
        --trace (show sensVars ++ show normVars) $
        ((numOfVars, leakedVars), (tableName, M.fromList $ zip sensVars normVars))
    else
        -- if the policy is not related to the given table, it is treated as public
        ((0, []), (tableName, M.empty))

