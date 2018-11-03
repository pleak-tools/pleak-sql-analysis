module PolicyQ where

import Control.Monad (void)
import Data.Bits
import Data.Either
import Data.List
import Data.List.Split
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Void
import Debug.Trace

import ErrorMsg
import ExprQ
import QueryQ
import NormsQ

-------------------------------
---- policy data structures ----
-------------------------------

data VarState
  = Exact | None | Approx Double | Total Int | Range Double Double 
  deriving (Show)

verifyVarSecrecy :: M.Map String VarState -> M.Map String VarState -> String -> (String, (Int, [Bool],[String],[Expr]))
verifyVarSecrecy attMap plcMap preficedVar =

    let [prefix,var] = case (splitOn "." preficedVar) of
                           [s1,s2] -> [s1,s2]
                           _       -> error $ error_badPolicyFormat preficedVar
    in
    let plcState = plcMap ! preficedVar in
    let attState = if M.member preficedVar attMap then attMap ! preficedVar else None in
    -- the cases in which the given attacker guesses the variable with required precision
    let leakedVar = case (attState, plcState) of
            (Exact,_)                -> [True]
            (Approx r1, Approx r2)   -> [r1 <= r2]
            (Total  n1, Total  n2)   -> [n1 <= n2]
            -- here we assume that the actual data belongs to (lb,ub) -- i.e. the attacker knowledge is correct
            -- while (ub - lb) / 2 <= r2 would already be sufficient in the case when the actual data is in the middle,
            -- we only claim immediate leakage if it leaks for sure
            (Range lb ub, Approx r2) -> [(ub - lb) <= r2]
            _                        -> [False]
    in

    -- the variable is not sensitive either if attacker already knows it, or we do not care about it
    let sensVar = case (attState, plcState) of
            (Exact,_) -> []
            (_, None) -> []
            _         -> [var]
    in

    -- constuct the norm, which is NormZero for insensitive vars, L0 for exact guesses, and is abs.value for approximated guesses
    -- TODO if we scale norm  by 1/r here, we will always have r = 1, but need to rescale R
    let normVar = case (attState, plcState) of
            (Exact,_)    -> []
            (_, None)    -> []
            (_,Exact)    -> [LZero var]
            (_,Approx r) -> [ScaleNorm (1/r) var]
            (_,Total _)  -> [LZero var]
            _ -> error $ error_badAttackerPolicyCombination attState plcState
    in

    (prefix, (1, leakedVar,sensVar,normVar))

-- TODO verify if we indeed want weight 1.0 for the projections
extract_bs :: M.Map String VarState -> M.Map String VarState -> [Bool]
extract_bs attMap plcMap =
    map (extract_b attMap plcMap) (M.keys plcMap)

-- check whether sensitivity w.r.t. that variable needs to be analysed at all
-- TODO check if there are more "False" cases
extract_b :: M.Map String VarState -> M.Map String VarState -> String -> Bool
extract_b attMap plcMap var =
    let plcState = plcMap ! var in
    let attState = if M.member var attMap then attMap ! var else None in
    case (attState, plcState) of
            (_, None)    -> False
            (Exact,_)    -> False
            _            -> True


extract_rs :: M.Map String VarState -> M.Map String VarState -> [Double]
extract_rs attMap plcMap =
    map (extract_r attMap plcMap) (M.keys plcMap)

extract_r :: M.Map String VarState -> M.Map String VarState -> String -> Double
extract_r attMap plcMap var =
    let plcState = plcMap ! var in
    let attState = if M.member var attMap then attMap ! var else None in
    case (attState, plcState) of
            (_,None)     -> 1.0 -- the dimensionality reduces, and multiplication by 1 does not change the result
            (_,Exact)    -> 1.0 -- 1 is compatible with L0-norm, and it assumes that R will be the number of possible choices
            (_,Approx r) -> r
            (_,Total _)  -> 1.0 -- this is used only for discrete variables, and we have no means to conceal 'r out of R' choices yet
            _ -> error $ error_badAttackerPolicyCombination attState plcState

extract_M :: M.Map String VarState -> M.Map String VarState -> Int
extract_M attMap plcMap =
    sum $ map (extract_m attMap plcMap) (M.keys plcMap)

extract_m :: M.Map String VarState -> M.Map String VarState -> String -> Int
extract_m attMap plcMap var =
    let plcState = plcMap ! var in
    let attState = if M.member var attMap then attMap ! var else None in
    case (attState, plcState) of
            (Exact,_) -> 0
            (_, None) -> 0
            _ -> 1

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
            (Exact,_)       -> 1.0 -- if the attacker already knows the value exactly, there is 1 possible choice
            (None, _)       -> let dataType = typeMap ! var in
                                   case dataType of
                                       "int8"   -> 2^32
                                       "float8" -> 2^32
                                       "bool"   -> 1.0 -- we have 2 choices, but the radius is 1
                                       _       -> error $ error_unboundedDataType dataType
            (Approx r,_)    -> r
            (Total _, _)    -> 1.0 -- this is used only for discrete variables, and we have no means to conceal 'r out of R' choices yet
                                   -- TODO actually, it seems that we can do it
            (Range lb ub,_) -> (ub - lb) / 2.0 -- best-case distance when the actual data point is in the middle,  we choose to overestimate the attacker

-- this is the same as R for continuous variables, but diffrent for ordinal
extract_CRs :: M.Map String VarState -> M.Map String String -> M.Map String VarState -> [Double]
extract_CRs attMap typeMap plcMap =
    map (extract_CR attMap plcMap typeMap) (M.keys plcMap)

extract_CR :: M.Map String VarState -> M.Map String VarState -> M.Map String String -> String -> Double
extract_CR attMap plcMap typeMap var =
    let plcState = plcMap ! var in
    let attState = if M.member var attMap then attMap ! var else None in
    case (attState, plcState) of
            (Exact,_)       -> 1.0 -- if the attacker already knows the value exactly, there is 1 possible choice
            (None, _)       -> let dataType = typeMap ! var in
                                   case dataType of
                                       "int8"   -> 2^32
                                       "float8" -> 2^32
                                       "bool"   -> 2.0 -- we have 2 choices, although the radius is 1
                                       _       -> error $ error_unboundedDataType dataType
            (Approx r,_)    -> r
            (Total n, _)    -> fromIntegral n
            (Range lb ub,_) -> (ub - lb) / 2.0 -- best-case distance when the actual data point is in the middle,  we choose to overestimate the attacker

-- TODO since we scale all repeating variables in the same way, we may take any of them (let it be the first one)
combineSets :: M.Map String Expr -> M.Map String Expr -> M.Map String Expr
combineSets m1 m2 = 
    M.unionWith const m1 m2

normsFromCombinedData :: M.Map TableName (M.Map String Expr) -> TableName -> (([Int], [VarName]), NormFunction, Maybe Double)
normsFromCombinedData combinedDataMap tableName =
    let varMap = combinedDataMap ! tableName in
    let sensVars = M.keys varMap in
    let normVars = M.elems varMap in
    let normVarNames = (map (\x -> "_nv" ++ show x) [0..(length normVars - 1)]) in
    let tempVarMap = M.fromList $ zip normVarNames normVars in
    let nf = NF (M.insert "_nv" (LInf normVarNames) tempVarMap) (SelectL 1.0 "_nv") in
    -- let all rows be sensitive by default, we will need additional input otherwise
    (([0..],sensVars),nf, Nothing)

constructNormData :: [TableName] -> M.Map String VarState -> [(M.Map String VarState, Double)] -> [(([Int], [VarName]), NormFunction, Maybe Double)]
constructNormData tableNames attMap plcMaps =
    -- we put together all variables of all sensitive sets to define one norm over all of them
    -- TODO we currently assume that, if a variable occurs in several sets, it still has the same sensitivity radius
    let temp = map (constructNormDataSet tableNames attMap . fst) plcMaps in
    let allTableMap = foldr (M.unionWith combineSets) M.empty temp in
    map (normsFromCombinedData allTableMap) tableNames

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
        trace (show sensVars ++ show normVars) $
        ((numOfVars, leakedVars), (tableName, M.fromList $ zip sensVars normVars))
    else
        -- if the policy is not related to the given table, it is treated as public
        ((0, []), (tableName, M.empty))

