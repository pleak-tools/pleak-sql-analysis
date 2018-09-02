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
import QueryQ
import NormsQ

-------------------------------
---- policy data structures ----
-------------------------------

data VarState
  = Exact | None | Approx Double | Range Double Double 
  deriving (Show)

verifyVarSecrecy :: TableName -> M.Map String VarState -> M.Map String VarState -> String -> (Bool,[String],Expr)
verifyVarSecrecy tableName attMap plcMap var =
    let plcState = plcMap ! var in
    let extVar = tableName ++ "." ++ var in
    let attState = if M.member extVar attMap then attMap ! extVar else None in
    --trace (extVar ++ " " ++ show attState ++ " " ++ show plcState) $ 
    -- the cases in which the given attacker guesses the variable with required precision
    let leakedVar = case (attState, plcState) of
            (Exact,_) -> True
            (Approx r1, Approx r2) -> (r1 <= r2)
            (Range lb ub, Approx r2) -> ((ub - lb) <= r2)
            _ -> False
    in

    -- the variable is not sensitive either if attacker already knows it, or we do not care about it
    let sensVar = case (attState, plcState) of
            (Exact,_) -> []
            (_, None) -> []
            _ -> [var]
    in

    -- constuct the norm, which is NormZero for insensitive vars, L0 for exact guesses, and is scaled L1-norm for approximated guesses
    let normVar = case (attState, plcState) of
            (Exact,_) -> ZeroSens var
            (_, None) -> ZeroSens var
            (_,Exact) -> LZero var
            (_,Approx r) -> ScaleNorm (1 / r) var
            _ -> error $ error_badAttackerPolicyCombination attState plcState
    in

    (leakedVar,sensVar,normVar)

-- TODO verify if we indeed want weight 1.0 for the projections
extract_rs :: TableName -> M.Map String VarState -> M.Map String VarState -> [Double]
extract_rs tableName attMap plcMap =
    map (extract_r tableName attMap plcMap) (M.keys plcMap)

extract_r :: TableName -> M.Map String VarState -> M.Map String VarState -> String -> Double
extract_r tableName attMap plcMap var =
    let plcState = plcMap ! var in
    let extVar = tableName ++ "." ++ var in
    let attState = if M.member extVar attMap then attMap ! extVar else None in
    case (attState, plcState) of
            (_,None)     -> 1.0
            (_,Exact)    -> 1.0
            (_,Approx r) -> r
            _ -> error $ error_badAttackerPolicyCombination attState plcState

extract_ms :: TableName -> M.Map String VarState -> M.Map String VarState -> Int
extract_ms tableName attMap plcMap =
    sum $ map (extract_m tableName attMap plcMap) (M.keys plcMap)

extract_m :: TableName -> M.Map String VarState -> M.Map String VarState -> String -> Int
extract_m tableName attMap plcMap var =
    let plcState = plcMap ! var in
    let extVar = tableName ++ "." ++ var in
    let attState = if M.member extVar attMap then attMap ! extVar else None in
    case (attState, plcState) of
            (Exact,_) -> 0
            (_, None) -> 0
            _ -> 1

extract_Rs :: TableName -> M.Map String VarState -> M.Map String VarState -> M.Map String String -> [Double]
extract_Rs tableName attMap plcMap typeMap =
    map (extract_R tableName attMap plcMap typeMap) (M.keys plcMap)

extract_R :: TableName -> M.Map String VarState -> M.Map String VarState -> M.Map String String -> String -> Double
extract_R tableName attMap plcMap typeMap var =
    let plcState = plcMap ! var in
    let extVar = tableName ++ "." ++ var in
    --trace (show attMap) $
    --trace (show plcMap) $
    --trace (show typeMap) $
    --trace "---------" $
    let attState = if M.member extVar attMap then attMap ! extVar else None in
    case (attState, plcState) of
            (Exact,_)       -> 1.0
            (None, _)       -> let dataType = typeMap ! extVar in
                                   case dataType of
                                       "INT8"   -> 2^32
                                       "FLOAT8" -> 2^32
                                       "BOOL"   -> 1.0
                                       "TEXT"   -> 1.0
                                       _       -> error $ error_unboundedDataType dataType
            (Approx r,_)    -> r
            (Range lb ub,_) -> (ub - lb) / 2.0

constructNormData :: TableName -> M.Map String VarState -> M.Map String VarState -> (([Int], [VarName]), NormFunction)
constructNormData tableName attMap plcMap =
    let vars = M.keys plcMap in
    -- find out which variables in the policy are already guessed by the attacker
    let (leakedVars,sensVars,normVars) = unzip3 $ map (verifyVarSecrecy tableName attMap plcMap) vars in
    let badAttacker = foldr (&&) True leakedVars in
    if (length vars > 0 && badAttacker) then error $ error_attackerBreaksEverything tableName else
    let normVarNames = (map (\x -> "_nv" ++ show x) [0..(length normVars - 1)]) in
    let tempVarMap = M.fromList $ zip normVarNames normVars in
    let nf = NF (M.insert "_nv" (L 1.0 normVarNames) tempVarMap) (SelectL 1.0 "_nv") in 
    (([0..],concat sensVars),nf)

