module PolicyQ where

import Control.Monad (void)
import Data.Bits
import Data.Char
import Data.Either
import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Void
import Debug.Trace

import ErrorMsg
import AexprQ
import ExprQ
import GroupQ
import QueryQ
import NormsQ
import VarstateQ

-- policy-related data structures
type PlcExpr     = AExpr ([String], VarState)
type PlcCostType = (PlcExpr,Double,[(String, AExpr VarName)])

getStatement (plcExpr,_,_) = plcExpr
getCost (_,cost,_) = cost
getFilters (_,_,fs) = fs

data PlcData = PlcData Bool Double Double Double Bool ([Either Double String] -> Double -> Maybe (Double,Double))
get_b  (PlcData b _  _ _ _ _) = b
get_ur (PlcData _ ur _ _ _ _) = ur
get_r  (PlcData _ _  r _ _ _) = r
get_rr (PlcData _ _ _ rr _ _) = rr
get_d  (PlcData _ _ _ _  d _) = d
get_g  (PlcData _ _ _ _ _  g) = g

instance Show PlcData where
   show (PlcData _ ur r rr _ _) = "(" ++ show ur ++ "," ++ show r ++ "," ++ show rr ++ ")"

type PlcMap = AExpr ([String],PlcData)

rewriteExpr :: (([String],VarState) -> ([String],PlcData)) -> PlcExpr -> PlcMap
rewriteExpr f plcExpr = 
    traverseExpr (ABinary AAnd) (ABinary AOr) AConst (\x -> AVar (f x)) plcExpr

-- table constraint data structure
type AttMap = M.Map String VarState

-- (relatively) nice norm printing
niceNormPrint :: (Show a) => Norm a -> String
niceNormPrint = niceNorm

niceADoublePrint :: ADouble -> String
niceADoublePrint = niceADouble

getRangeLB (Range lb _ ) = lb
getRangeUB (Range _  ub) = ub

-- this is NOT our contribution, and is taken directly from https://www.johndcook.com/blog/haskell-erf/
erf :: Double -> Double
erf x = sign*y
    where
        a1 =  0.254829592
        a2 = -0.284496736
        a3 =  1.421413741
        a4 = -1.453152027
        a5 =  1.061405429
        p  =  0.3275911

        -- Abramowitz and Stegun formula 7.1.26
        sign = if x > 0 then 1 else -1
        t  =  1.0/(1.0 + p* abs x)
        y  =  1.0 - (((((a5*t + a4)*t) + a3)*t + a2)*t + a1)*t*exp(-x*x)

-- traverse the aexpr formula
-- apply the function fvar to a variable and fconst to a constant
-- combine the results using the functions fand and for
traverseExpr :: (a -> a -> a) -> (a -> a -> a) -> (Double -> a) -> (b -> a) -> (AExpr b) -> a
traverseExpr _ _ _ fvar (AVar x) =
    fvar x

traverseExpr _ _ fconst _ (AConst x) =
    fconst x

traverseExpr fand for fconst fvar (ABinary AAnd x1 x2) =
    let y1 = traverseExpr fand for fconst fvar x1 in
    let y2 = traverseExpr fand for fconst fvar x2 in
    fand y1 y2

traverseExpr fand for fconst fvar (ABinary AOr x1 x2) =
    let y1 = traverseExpr fand for fconst fvar x1 in
    let y2 = traverseExpr fand for fconst fvar x2 in
    for y1 y2

-- we know that, if the variable is the same, then only the r part can be different
minPlcData (PlcData b ur r1 rr d g) (PlcData _ _ r2 _ _ _) =
    (PlcData b ur (min r1 r2) rr d g)

-- compute p and q using the equalities P(A \/ B) = P(A) + P(B) - P(AB), P(A /\ A) = P(A), P(A /\ B) = P(A)*P(B)

-- if the same variable repeats with different precisions, we need to take minimum in an AND
fand :: [(Int, M.Map [String] PlcData)] -> [(Int, M.Map [String] PlcData)] -> [(Int, M.Map [String] PlcData)]
fand ms1 ms2 = concat $ map (\(s2,m2) -> map (\(s1,m1) -> (s1*s2, M.unionWith minPlcData m1 m2)) ms1) ms2

for  :: [(Int, M.Map [String] PlcData)] -> [(Int, M.Map [String] PlcData)] -> [(Int, M.Map [String] PlcData)]
for ms1 ms2 = ms1 ++ ms2 ++ map (\(s,v) -> (-s,v)) (fand ms1 ms2)

computePweights plcExpr = traverseExpr fand for (\x -> if x == 1 then [(1,M.empty)] else []) (\(var,pd) -> [(1, M.singleton var pd)]) plcExpr


-- collect the variables that are part of lp-norm approximation for p > 1
-- we currently assume that such variables are
findLpVars :: AExpr ([String],Double,b) -> [String]
findLpVars (AVar (xs,p,_)) = if p > 1 && length xs > 1 then xs else []
findLpVars (AConst x) = []
findLpVars (ABinary AAnd x1 x2) = findLpVars x1 ++ findLpVars x2
findLpVars (ABinary AOr x1 x2)  = findLpVars x1 ++ findLpVars x2

-- verify the "goodness" of attacker and policy states
isBadPlcState :: VarState -> (Bool,String)
isBadPlcState x =
    case x of
            Exact           -> (False,"")
            None            -> (False,"")
            Approx r        -> if r >= 0 then (False,"") else (True, err_badPolicy_r x)
            ApproxWrtLp _ r -> if r >= 0 then (False,"") else (True, err_badPolicy_r x)
            ApproxWrtLinf r -> if r >= 0 then (False,"") else (True, err_badPolicy_r x)
            _ -> (True, err_badPolicy x)

isBadAttState :: VarState -> (Bool,String)
isBadAttState x =
    case x of
            Exact -> (False,"")
            None  -> (False,"")

            Total   n     -> if n >= 0 then (False,"") else (True, err_badAttackerPolicy_n x)
            TotalUn n     -> if n >= 0 then (False,"") else (True, err_badAttackerPolicy_n x)

            Range   lb ub -> if lb <= ub then (False,"") else (True, err_badAttackerPolicy_range x)
            RangeUn lb ub -> if lb <= ub then (False,"") else (True, err_badAttackerPolicy_range x)
            RangePr lb mp -> let prs = M.elems mp in
                             let ubs = M.keys  mp in
                             if length (filter (< 0) prs) == 0 && abs(sum prs - 1) < 0.000001 then
                                 if length (filter (< lb) ubs) == 0 then (False,"")
                                 else (True, err_badAttackerPolicy_range x)
                             else (True, err_badAttackerPolicy_Pr x)

            SubSet _       -> (False,"")
            SubSetUn _     -> (False,"")
            SubSetPr mp    -> let prs = M.elems mp in
                              if length (filter (< 0) prs) == 0 && abs(sum prs - 1) < 0.000001 then (False,"")
                              else (True, err_badAttackerPolicy_Pr x)

            IntSubSet _    -> (False,"")
            IntSubSetUn _  -> (False,"")
            IntSubSetPr mp -> let prs = M.elems mp in
                              if length (filter (< 0) prs) == 0 && abs(sum prs - 1) < 0.000001 then (False,"")
                              else (True, err_badAttackerPolicy_Pr x)

            Normal mu sigma -> if sigma >= 0 then (False,"") else (True, err_badAttackerPolicy_normal sigma)

            _ -> (True, err_badAttackerPolicy x)

-- get all possible values from a state description
getStateValues :: M.Map String VarState -> String -> [Either Int String]
getStateValues attMap varName =
    if M.member varName attMap then
        let varState = (attMap ! varName) in
            case varState of
                Range   x y  -> map (Left . round) [x..(y-1)]
                RangeUn x y  -> map (Left . round) [x..(y-1)]
                RangePr x mp -> let y = getUb x mp in map (Left . round) [x..(y-1)]

                SubSet   xs -> map Right xs
                SubSetUn xs -> map Right xs
                SubSetPr mp -> map Right $ M.keys mp

                IntSubSet   xs -> map Left xs
                IntSubSetUn xs -> map Left xs
                IntSubSetPr mp -> map Left $ M.keys mp

                Normal _ _ -> error $ error_floatAttMapBounds varName varState

                _ -> error $ error_badAttMapBounds varName varState
    else error $ error_noAttMapBounds varName

-- the cases in which the given attacker guesses the variable with required precision
-- when matching range vs radius, or different lp-norms, we assume the worst-case attacker
isLeakedVar :: VarState -> VarState -> Bool
isLeakedVar plcState attState =
    case (attState, plcState) of

            (Exact,_)  -> True
            (None, _)  -> False
            (_, Exact) -> False
            (_, None)  -> False

            -- here we assume that the actual data belongs to (lb,ub) -- i.e. the attacker knowledge is correct
            -- in the worst case (ub - lb) / 2 <= r is sufficient for the attacker the case when the actual data is in the middle
            -- so claim that there are no privacy guarantees in such a case
            (Range   lb ub,  Approx r) -> (ub - lb) <= r
            (RangeUn lb ub,  Approx r) -> (ub - lb) <= r
            (RangePr lb ubs, Approx r) -> (sum $ map (\ub -> if (ub - lb) / 2 <= r then ubs ! ub else 0) (M.keys ubs)) == 1
            (Normal mu sigma, Approx r) -> 3 * (sqrt 2) * sigma <= r

            (Range   lb ub,  ApproxWrtLp _ r) -> (ub - lb) <= r
            (RangeUn lb ub,  ApproxWrtLp _ r) -> (ub - lb) <= r
            (RangePr lb ubs, ApproxWrtLp _ r) -> (sum $ map (\ub -> if (ub - lb) / 2 <= r then ubs ! ub else 0) (M.keys ubs)) == 1
            (Normal mu sigma,  ApproxWrtLp _ r) -> 3 * (sqrt 2) * sigma <= r

            (Range   lb ub,  ApproxWrtLinf r) -> (ub - lb) <= r
            (RangeUn lb ub,  ApproxWrtLinf r) -> (ub - lb) <= r
            (RangePr lb ubs, ApproxWrtLinf r) -> (sum $ map (\ub -> if (ub - lb) / 2 <= r then ubs ! ub else 0) (M.keys ubs)) == 1
            (Normal mu sigma, ApproxWrtLinf r) -> 3 * (sqrt 2) * sigma <= r

            _ -> error $ error_badAttackerPolicyCombination attState plcState


-- the variable is not sensitive either if attacker already knows it, or we do not care about it
isSensVar :: VarState -> VarState -> Bool
isSensVar plcState attState =
    if isLeakedVar plcState attState then False
    else case (attState, plcState) of
            (_, None) -> False
            _         -> True

-- TODO it seems that we should distinguish AND and OR, since a complete leakage in an AND can still be bearable
verifyVarsSecrecy :: M.Map String VarState -> M.Map [String] Double -> PlcExpr -> [(String, (Int, [Bool],[VarName],[VarName],M.Map String Expr))]
verifyVarsSecrecy attMap scaleMap plcExpr =
    traverseExpr (++) (++) (const []) (\(x,y) -> [verifyVarSecrecy attMap scaleMap y x]) plcExpr

verifyVarSecrecy :: M.Map String VarState -> M.Map [String] Double -> VarState -> [String] -> (String, (Int, [Bool],[VarName],[VarName],M.Map String Expr))
verifyVarSecrecy attMap scaleMap plcState preficedVs =

    let (prefices,vs) = unzip $ map (\pv -> case varNameToTableAndSubVarName pv of
                                                [s1,s2] -> (s1,s2)
                                                _       -> error $ error_badPolicyFormat pv) preficedVs
    in

    -- it is not allowed to mix columns of different tables into an lp-norm
    if S.size (S.fromList prefices) == 0 then error $ error_badPolicyFormatEmptyVars else
    if S.size (S.fromList prefices) > 1  then error $ error_badPolicyFormatLpMixedTables prefices else
    let prefix = head prefices in

    let attStates = map (\pv -> if M.member pv attMap then attMap ! pv else None) preficedVs in

    let leakedVars = map (isLeakedVar plcState) attStates in
    let sensVars   = filterWith (map (isSensVar plcState) attStates) vs in

    -- this is to create temporary variables for the norm construction
    let sensVarKeys = map ("~" ++) sensVars in

    -- constuct the norm, which is NormZero for insensitive vars, L0 for exact guesses, and Lp-norm for approximated guesses
    let (normKeys,normMap) = case plcState of
            None            -> ([],M.empty)
            Exact           -> (sensVarKeys, M.fromList $ zip sensVarKeys (map LZero sensVars))
            Approx        _ -> (sensVarKeys, let r = scaleMap ! preficedVs in M.fromList $ zip sensVarKeys (map (ScaleNorm (1/r)) sensVars))
            ApproxWrtLp p _ -> let x1 = intercalate "_" sensVars in
                               let x2 = "~" ++ x1 in
                               let r = scaleMap ! preficedVs in
                               ([x1], M.fromList [(x1, ScaleNorm (1/r) x2), (x2, L p sensVars)])
            ApproxWrtLinf _ -> let x1 = intercalate "_" sensVars in
                               let x2 = "~" ++ x1 in
                               let r = scaleMap ! preficedVs in
                               ([x1], M.fromList [(x1, ScaleNorm (1/r) x2), (x2, LInf sensVars)])
            _ -> error $ err_badPolicy plcState
    in

    (prefix, (1, leakedVars,sensVars,normKeys,normMap))

-- extract variable names
extract_vars :: PlcExpr-> [[String]]
extract_vars plcExpr =
    traverseExpr (++) (++) (const []) (\(x,y) -> [x]) plcExpr

-- extract variable states
extract_states :: PlcExpr-> [VarState]
extract_states plcExpr =
    traverseExpr (++) (++) (const []) (\(x,y) -> [y]) plcExpr

-- check whether sensitivity w.r.t. that variable needs to be analysed at all
extract_bs :: M.Map String VarState -> PlcExpr -> [Bool]
extract_bs attMap plcExpr =
    traverseExpr (++) (++) (const []) (\(x,y) -> [extract_b attMap y x]) plcExpr

extract_b :: M.Map String VarState -> VarState -> [String] -> Bool
extract_b attMap plcState vs =
    -- if at least one variable in the approximated vector is sensitive, then we do consider it in the analysis
    let sensVars = map (\v -> let attState = if M.member v attMap then attMap ! v else None in isSensVar plcState attState) vs in
    foldr (||) False sensVars

-- extract the guessing radius
extract_rs :: M.Map String VarState -> PlcExpr -> [Double]
extract_rs attMap plcExpr =
    traverseExpr (++) (++) (const []) (\(_,y) -> [extract_r y]) plcExpr

extract_r :: VarState -> Double
extract_r plcState =
    case plcState of
            Exact           -> 1.0 -- compatible with L0-norm
            Approx        r -> r
            ApproxWrtLp _ r -> r
            ApproxWrtLinf r -> r
            _ -> error $ err_badPolicy plcState

-- extract whether the dimension has discrete norm
extract_ds :: M.Map String VarState -> PlcExpr -> [Bool]
extract_ds attMap plcExpr =
    traverseExpr (++) (++) (const []) (\(x,y) -> [extract_d y]) plcExpr

extract_d :: VarState -> Bool
extract_d plcState =
    case plcState of
            Exact           -> True
            Approx r        -> False
            ApproxWrtLp _ r -> False
            ApproxWrtLinf r -> False
            _ -> error $ err_badPolicy plcState

-- extract the used p-norm
extract_ps :: M.Map String VarState -> PlcExpr -> [Double]
extract_ps attMap plcExpr =
    traverseExpr (++) (++) (const []) (\(x,y) -> [extract_p y]) plcExpr

extract_p :: VarState -> Double
extract_p plcState =
    case plcState of
            Exact           -> 0.0
            Approx r        -> 1.0
            ApproxWrtLp p r -> p
            ApproxWrtLinf r -> 1/0
            _ -> error $ err_badPolicy plcState

-- extract the function computing probabilities in total space
-- we let 'g' return two outputs: the probability 'p', as well as max-distance (which can be different from initial 'a')
extract_gs :: M.Map String VarState -> PlcExpr -> [[Either Double String] -> Double -> Maybe (Double,Double)]
extract_gs attMap plcExpr =
    traverseExpr (++) (++) (const []) (\(xs,_) -> [extract_g attMap xs]) plcExpr

-- vs is the vector being approximated
-- we assume that attacker known bounds hold w.r.t. the same lp-norm that is used by vs
-- otherwise, it would be more complicated to compute the weight of a circle w.r.t. a square, and using same lp-norm is more reasonable
extract_g :: M.Map String VarState -> [String] -> ([Either Double String] -> Double -> Maybe (Double,Double))
extract_g attMap vs =
  let attStates = map (\v -> if M.member v attMap then attMap ! v else None) vs in
  let fs = map (\attState ->
          case attState of
            Exact        -> const $ const $ Just (1.0, 1.0)   -- a leaked sensitive region has probability weight 1
            None         -> const $ const Nothing             -- no knowledge

            -- unknown distribution
            Total n      -> const $ const Nothing
            SubSet xs    -> const $ const Nothing
            IntSubSet xs -> const $ const Nothing
            Range lb ub  -> const $ const Nothing

            -- uniform distribution
            -- since the distance does not depend on x, it always makes sense to take the entire space for r > 1
            TotalUn n      -> (\_ r -> if r == 1 then Just (1.0 / fromIntegral n, 1.0) else Just (1.0,1.0))
            SubSetUn xs    -> let n = length xs in (\_ r -> if r == 1 then Just (1 / fromIntegral n, 1.0) else Just (1.0,1.0))
            IntSubSetUn xs -> let n = length xs in (\_ r -> if r == 1 then Just (1 / fromIntegral n, 1.0) else Just (1.0,1.0))
            -- here the distance does depend on both r and x
            RangeUn lb ub  -> (\z r -> case z of
                                           Left x -> let xub = min (x + r) ub in
                                                     let xlb = max (x - r) lb in
                                                     Just ((xub - xlb) / (ub - lb), xub - xlb)
                                           Right x -> error $ error_badPolicyString x)

            -- customized distribution
            -- we take "g a = 1" for a > 1
            -- we do not define lp-norms over discrete sets
            SubSetPr mp    -> if length vs > 1 then error $ error_badPolicyFormatLpDiscrete vs
                              else (\z r -> case z of
                                                Left x  -> error $ error_badPolicyDouble x
                                                Right x -> if r == 1 then
                                                              if M.member x mp then Just (mp ! x, 1.0) else error $ error_badPolicyFormatUnknownSetVar x mp
                                                           else Just (1.0,1.0))

            IntSubSetPr mp -> if length vs > 1 then error $ error_badPolicyFormatLpDiscrete vs
                              else (\z r -> case z of
                                                Right x -> error $ error_badPolicyString x
                                                Left x  -> if r == 1 then
                                                              let xx = round x in
                                                              if M.member xx mp then Just (mp ! xx, 1.0) else error $ error_badPolicyFormatUnknownSetVar xx mp
                                                           else Just (1.0,1.0))

            -- if the range is given in several segments, we assume that the distribution inside each segment is uniform
            RangePr lb mp -> (\z r -> case z of
                                          Right x -> error $ error_badPolicyString x
                                          Left x ->
                                              let ub = foldr max lb (M.keys mp) in
                                              let xub = min (x + r) ub in
                                              let xlb = max (x - r) lb in

                                              -- compute the total weight of blocks fully in (x-r,x+r)
                                              let xLD = dropWhile (<= x - r) (M.keys mp) in
                                              let xLT = takeWhile (<= x - r) (M.keys mp) in
                                              let xRD = dropWhile (<  x + r) (M.keys mp) in
                                              let xRT = takeWhile (<  x + r) (M.keys mp) in

                                              let (lbR, xLD0) = if length xLD == 0 then (ub, []) else (head xLD, tail xLD) in
                                              let pkeys = S.toList $ S.intersection (S.fromList xLD0) (S.fromList xRT) in
                                              let p1 = sum $ map (mp ! ) pkeys in

                                              -- include those partially in (x-r,x+r)
                                              let lbL = if length xLT == 0 then lb else last xLT in
                                              let ubL = if length xRT == 0 then lb else last xRT in
                                              let ubR = if length xRD == 0 then ub else last xRD in

                                              let p2 = if ubL == ubR then 0 else (mp ! ubR) * (xub - ubL) / (ubR - ubL) in
                                              let p3 = if lbL == lbR then 0 else (mp ! lbR) * (lbR - xlb) / (lbR - lbL) in
                                              let p0 = p2 + p3 - (if ubL == lbL then (mp ! ubR) else 0) in

                                              Just (p1 + p0, xub - xlb))

            Normal mu sigma -> (\z r -> case z of
                                            Right x -> error $ error_badPolicyString x
                                            Left  x -> Just ((erf ((abs (x - mu) + r) / (sigma * (sqrt 2))) - erf ((abs (x - mu) - r) / (sigma * (sqrt 2)))) / 2.0, 2.0 * r))

            _ -> error $ err_badAttackerPolicy attState) attStates in

  -- if we do not know some dimension, then the total weight is unknown as well
  (\xs r ->
          let ws = zipWith (\f x -> f x r) fs xs in
          if elem Nothing ws then Nothing else
          let (zs,as) = unzip $ map fromJust ws in
          Just (product zs, foldr max 1 as))

-- extract the total space radius
-- assume that attacker known bounds hold w.r.t. the same lp-norm that is used in sensitive set
extract_Rs :: M.Map String VarState -> M.Map String String -> PlcExpr -> [Double]
extract_Rs attMap typeMap plcExpr =
    traverseExpr (++) (++) (const []) (\(x,y) -> [extract_R attMap typeMap y x]) plcExpr

extract_R :: M.Map String VarState -> M.Map String String -> VarState -> [String] -> Double
extract_R attMap typeMap plcState vs =
    let rrs = map (\var -> 
          let attState = if M.member var attMap then attMap ! var else None in
          case (attState, plcState) of
            (Exact,_)       -> 1.0 -- compatible with L0-norm
            (None, Exact)   -> 1.0 -- compatible with L0-norm
            (None, _)       -> let dataType = map toLower $ typeMap ! var in
                                   case dataType of
                                       "int"   -> 2^64
                                       "bool"   -> 2.0
                                       _        -> 1/0

            (Total n, _)       -> fromIntegral $ n
            (TotalUn n, _)     -> fromIntegral $ n

            (SubSet   xs,_)    -> fromIntegral $ length xs
            (SubSetUn xs,_)    -> fromIntegral $ length xs
            (SubSetPr mp,_)    -> fromIntegral $ M.size mp

            (IntSubSet   xs,_) -> fromIntegral $ length xs
            (IntSubSetUn xs,_) -> fromIntegral $ length xs
            (IntSubSetPr mp,_) -> fromIntegral $ M.size mp

            (Range   lb ub,_)  -> (ub - lb) / 2.0
            (RangeUn lb ub,_)  -> (ub - lb) / 2.0
            (RangePr lb mp,_)  -> let ub = getUb lb mp in (ub - lb) / 2.0

            -- although normal distribution is infinite, we take '3 * (sqrt 2) * sigma', which covers erf(3) ~ 0.9999779 of the space
            (Normal _ sigma,_)  -> 3 * (sqrt 2) * sigma

            _ -> error $ err_badAttackerPolicy attState) vs
    in
    case plcState of
        Exact           -> lpnorm 1.0 rrs
        Approx _        -> lpnorm 1.0 rrs
        ApproxWrtLp p _ -> lpnorm p rrs
        ApproxWrtLinf _ -> linfnorm rrs

-- compute ||(x_1,...,x_n)||_p
lpnorm :: Double -> [Double] -> Double
lpnorm p xs = (sum $ map (** p) $ map abs xs) ** (1 / p)

-- compute ||(x_1,...,x_n)||_infinity
linfnorm :: [Double] -> Double
linfnorm = maximum . map abs

doubleRangesToAexprRanges :: M.Map String VarState -> M.Map String (VState (AExpr a))
doubleRangesToAexprRanges attMap =
    let rangeAttMap = M.filter (\x -> case x of
                                          Range _ _ -> True
                                          RangeUn _ _ -> True
                                          RangePr _ _ -> True
                                          _ -> False) attMap in

    M.map (\x -> case x of
                     Range lb ub -> Range (AConst lb) (AConst ub)
                     RangeUn lb ub -> Range (AConst lb) (AConst ub)
                     RangePr lb mp -> let ub = getUb lb mp in Range (AConst lb) (AConst ub)) rangeAttMap

-- update varstates of the attacker file if their type is not compatible with the schema
update_varStates :: M.Map String VarState -> M.Map String String -> M.Map String VarState
update_varStates attMap typeMap =
    let newAttMap   = map (update_varState attMap typeMap) (M.keys attMap) in
    let badTypeVars = filter (\(x,t) -> case t of Nothing -> True; _ -> False) newAttMap in
    if (length badTypeVars > 0) then error $ error_badAttackerTypes badTypeVars
    else M.fromList $ map (\(x, Just t) -> (x, t)) newAttMap

update_varState :: M.Map String VarState -> M.Map String String -> String -> (String, Maybe VarState)
update_varState attMap typeMap var =
    let attState = attMap ! var in
    if not (M.member var typeMap) then (var, Just attState)
    else
        case (attState, map toLower (typeMap ! var)) of
            (Exact,_)   -> (var, Just attState)
            (None, _)   -> (var, Just attState)

            -- a discrete set of size more than 2 is not compatible with booleans
            (Total n,   t)     -> if t == "bool" && n > 2 then (var, Nothing) else (var, Just attState)
            (TotalUn n, t)     -> if t == "bool" && n > 2 then (var, Nothing) else (var, Just attState)

            -- we do not check how exactly the set elements are named in a discrete set
            (SubSet   xs,t)    -> if t == "bool" && (length xs) > 2 then (var, Nothing)
                                  else (var, Just attState)

            (SubSetUn xs,t)    -> if t == "bool" && (length xs) > 2 then (var, Nothing)
                                  else (var, Just attState)

            (SubSetPr mp,t)    -> if t == "bool" && (M.size mp) > 2 then (var, Nothing)
                                  else (var, Just attState)

            -- an integer discrete set is compatible with int and float
            (IntSubSet   xs,t) -> if t == "bool" && (length xs) > 2 then (var, Nothing)
                                  else if t == "int" || t == "float" then (var, Just attState)
                                  else (var, Just $ SubSet   $ map show xs)

            (IntSubSetUn xs,t) -> if t == "bool" && (length xs) > 2 then (var, Nothing)
                                  else if t == "int" || t == "float" then (var, Just attState)
                                  else (var, Just $ SubSetUn $ map show xs)

            (IntSubSetPr mp,t) -> if t == "bool" && (M.size mp) > 2 then (var, Nothing)
                                  else if t == "int" || t == "float" then (var, Just attState)
                                  else (var, Just $ SubSetPr $ M.mapKeys show mp)

            -- a range is compatible with int and float
            (Range   lb ub,t)  -> if t == "int" || t == "float" then (var, Just attState) else (var, Nothing)
            (RangeUn lb ub,t)  -> if t == "int" || t == "float" then (var, Just attState) else (var, Nothing)
            (RangePr lb mp,t)  -> if t == "int" || t == "float" then (var, Just attState) else (var, Nothing)

            -- normal distribution is compatible with int and float
            (Normal mu sigma,t)  -> if t == "int" || t == "float" then (var, Just attState) else (var, Nothing)
            _ -> error $ err_badAttackerPolicy attState

filterWith [] [] = []
filterWith (b:bs) (x:xs) =
    let ys = filterWith bs xs in
    if b then (x:ys) else ys

-- construct the norm w.r.t. which we compute sensitivity -- the construction that we actually use in the analysis, with optimizations
constructNormData :: [TableName] -> M.Map String VarState -> PlcExpr -> [(([Int], [VarName]), NormFunction, Maybe Double)]
constructNormData tableNames attMap plcExpr =

    -- check that the attacker knowledge and the sensitive variables have been defined correctly
    let badAttStates = map isBadAttState $ M.elems attMap in

    let plcMapVars   = extract_vars   plcExpr in
    let plcMapStates = extract_states plcExpr in

    let badPlcStates = map isBadPlcState plcMapStates in
    let badStates = badAttStates ++ badPlcStates in
    let (somethingBad,errorMessages) = foldr (\(b1,e1) (b2,e2) -> (b1 || b2, if e1 == "" then e2 else e1 ++ ";\n" ++ e2)) (False,"") badStates in
    if somethingBad then error errorMessages else

    -- we put together all variables of all sensitive sets to define one norm over all of them
    let bs  = extract_bs attMap plcExpr in
    let xss = filterWith bs $ plcMapVars in
    let ds  = filterWith bs $ extract_ds attMap plcExpr in
    let rs  = filterWith bs $ extract_rs attMap plcExpr in

    -- if the same variable repeats with different precisions, we agree that we scale the space by the minimum to keep r <= 1
    let scaleMap' = M.fromListWith (\(d,r1) (_,r2) -> if d then (d,1.0) else (d,max r1 r2)) $ zip xss (zip ds rs) in
    let scaleMap  = M.map snd scaleMap' in

    let combinedDataMap = constructNormDataSet tableNames attMap scaleMap plcExpr in

    --let tableSensRows = map (extractRange plcExpr) tableNames in
    -- we decided not to introduce special variables for defining sensRows, but use row filters instead
    --let tableSensRows = replicate (length tableNames) [(0 :: Int)..] in
    -- TODO something is wrong afterwards in CreateTablesQ, we get something worse than [0..] for a table
    let tableSensRows = replicate (length tableNames) [] in

    zipWith (normsFromCombinedData combinedDataMap) tableNames tableSensRows



-- construct the norm w.r.t. which we compute sensitivity (used only for the output; this is the 'database norm' that should be understandable to the user)
-- TODO should we apply bss filter, or leave everything as it is?
deriveDbNorm :: M.Map String VarState -> PlcExpr -> Norm String
deriveDbNorm attMap plcExpr =

    -- we put together all variables of all sensitive sets to define one norm over all of them
    let bs  = extract_bs attMap plcExpr in
    let xss = filterWith bs $ extract_vars   plcExpr in
    let rs  = filterWith bs $ extract_rs attMap plcExpr in
    let ps  = filterWith bs $ extract_ps attMap plcExpr in

    -- if the same variable repeats with different precisions, we agree that we scale the space by the minimum to keep r <= 1
    let scaleMap = M.fromListWith (\(p,r1) (_,r2) -> (p, max r1 r2)) $ zip xss (zip ps rs) in
    let ys  = map (\ (xs, (p,r)) -> if p == 0 then NormLZero (Col (head xs)) else NormScale (1/r) (if p < 1/0 then NormL (Exactly p) (map Col xs) else NormL Any (map Col xs)) ) (M.toList scaleMap) in
    NormL Any ys

normsFromCombinedData :: M.Map TableName ([VarName],[VarName],M.Map String Expr) -> TableName -> [Int] -> (([Int], [VarName]), NormFunction, Maybe Double)
normsFromCombinedData combinedDataMap tableName tableSensRows =

    let (sensVars,normKeys,normMap) = combinedDataMap ! tableName in
    let nf = NF (M.insert defaultNormVariable (LInf $ nub normKeys) normMap) (SelectL 1.0 defaultNormVariable) in

    -- if there are no explicit records for sensitive rows, we consider all of them sensitive by deafult
    let recordedTableSensRows = if length tableSensRows == 0 then [0..] else tableSensRows in
    ((recordedTableSensRows,sensVars),nf, Nothing)

constructNormDataSet :: [TableName] -> M.Map String VarState -> M.Map [String] Double -> PlcExpr -> M.Map TableName ([VarName],[VarName],M.Map String Expr)
constructNormDataSet tableNames attMap scaleMap plcExpr =

    -- aggregate the variables for each table separately
    let dataMap = M.fromListWith (\(n1,x1s,y1s,z1s,w1s) (n2,x2s,y2s,z2s,w2s) -> (n1 + n2, x1s ++ x2s, y1s ++ y2s, z1s ++ z2s, M.union w1s w2s)) $ verifyVarsSecrecy attMap scaleMap plcExpr in

    --trace (show dataMap) $
    let (res0,res) = unzip $ map (constructTableNormData dataMap) tableNames in
    let (allNumOfVars, allLeakedVars) = unzip res0 in

    let numOfVars  = sum allNumOfVars in
    let leakedVars = concat allLeakedVars in

    -- find out which variables in the policy are already guessed by the attacker
    let badAttacker = foldr (&&) True leakedVars in
    if (numOfVars > 0 && badAttacker) then error $ error_attackerBreaksEverything else M.fromList res

-- the attacker badness should be checked for all tables together, not one by one
constructTableNormData :: M.Map String (Int, [Bool],[VarName],[VarName],M.Map String Expr) -> String -> ((Int, [Bool]), (TableName, ([VarName],[VarName],M.Map String Expr)))
constructTableNormData dataMap tableName =

    if M.member tableName dataMap then
        let (numOfVars, leakedVars, sensVars, normKeys, normMap) = dataMap ! tableName in
        ((numOfVars, leakedVars), (tableName, (sensVars,normKeys,normMap)))
    else
        -- if the policy is not related to the given table, it is treated as public
        ((0, []), (tableName, ([],[],M.empty)))

