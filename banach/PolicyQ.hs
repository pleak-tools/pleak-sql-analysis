module PolicyQ where

import Control.Monad (void)
import Data.Bits
import Data.Char
import Data.Either
import Data.List
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

data PlcData = PlcData Bool Double Double Double Bool (Double -> Maybe [Double])
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

            (Range   lb ub,  ApproxWrtLp _ r) -> (ub - lb) <= r
            (RangeUn lb ub,  ApproxWrtLp _ r) -> (ub - lb) <= r
            (RangePr lb ubs, ApproxWrtLp _ r) -> (sum $ map (\ub -> if (ub - lb) / 2 <= r then ubs ! ub else 0) (M.keys ubs)) == 1

            (Range   lb ub,  ApproxWrtLinf r) -> (ub - lb) <= r
            (RangeUn lb ub,  ApproxWrtLinf r) -> (ub - lb) <= r
            (RangePr lb ubs, ApproxWrtLinf r) -> (sum $ map (\ub -> if (ub - lb) / 2 <= r then ubs ! ub else 0) (M.keys ubs)) == 1

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
extract_gs :: M.Map String VarState -> PlcExpr -> [Double -> Maybe [Double]]
extract_gs attMap plcExpr =
    traverseExpr (++) (++) (const []) (\(xs,_) -> [extract_g attMap xs]) plcExpr

-- we assume that attacker known bounds hold w.r.t. the same lp-norm that is used in sensitive set
-- otherwise, it would be more complicated to compute the weight of a circle w.r.t. a square, and using same lp-norm is more reasonable
extract_g :: M.Map String VarState -> [String] -> (Double -> Maybe [Double])
extract_g attMap vs =
  let attStates = map (\v -> if M.member v attMap then attMap ! v else None) vs in
  let fs = map (\attState ->
          case attState of
            Exact        -> const $ Just [1.0]   -- a leaked sensitive region has probability weight 1
            None         -> const Nothing        -- no knowledge

            -- unknown distribution
            Total n      -> const Nothing
            SubSet xs    -> const Nothing
            IntSubSet xs -> const Nothing
            Range lb ub  -> const Nothing

            -- uniform distribution
            -- since the distance does not depend on x, it always makes sense to take the entire space for a > 1
            TotalUn n      -> (\x -> if x == 1 then Just [1 / fromIntegral n] else Just [1.0])
            SubSetUn xs    -> let n = length xs in (\x -> if x == 1 then Just [1 / fromIntegral n] else Just [1.0])
            IntSubSetUn xs -> let n = length xs in (\x -> if x == 1 then Just [1 / fromIntegral n] else Just [1.0])
            -- here the distance does depend on x
            RangeUn lb ub  -> let rr = (ub - lb) / 2.0 in (\x -> Just [x / rr])

            -- customized distribution
            -- we look at all possiblilities for "g 1", and take "g a = 1" for a > 1
            -- we do not define lp-norms over discrete sets
            SubSetPr mp    -> if length vs > 1 then error (error_badPolicyFormatLpDiscrete vs) else (\x -> if x == 1 then Just (M.elems mp) else Just (replicate (M.size mp) 1.0))
            IntSubSetPr mp -> if length vs > 1 then error (error_badPolicyFormatLpDiscrete vs) else (\x -> if x == 1 then Just (M.elems mp) else Just (replicate (M.size mp) 1.0))

            -- if the range is given in several segments, we assume that the distribution inside each segment is uniform
            -- TODO can we do something better?
            RangePr lb mp  -> (\x ->
                                       -- compute the weight of blocks that are fully under x
                                       let p1 = sum $ map (\ub -> if ub - lb <= x then mp ! ub else 0) (M.keys mp) in
                                       -- compute the partial weight of the block where x locates
                                       let ubsL = takeWhile (<= x) (M.keys mp) in
                                       let ubsR = dropWhile (<  x) (M.keys mp) in
                                       let ubL = if length ubsL > 0 then last ubsL else lb in
                                       let ubR = if length ubsR > 0 then head ubsR else getUb lb mp in
                                       let p2 = if ubL == ubR then 0 else ((x + lb) - ubL) / (ubR - ubL) * (mp ! ubR) in
                                       Just [p1 + p2])

            _ -> error $ err_badAttackerPolicy attState) attStates in

  -- for discrete variables, we cannot have longer combinations of lp-norms
  if length vs == 1 then head fs else
  -- if we do not know some dimension, then the total weight is unknown as well
  if elem Nothing (zipWith (\f x -> f x) fs (replicate (length fs) 0)) then const Nothing else
  (\r ->
          -- if all variables are non-discrete, then we have exactly one element in each list under Just
          let zs = map (\f -> (head . (\(Just z) -> z) . f) r) fs in
          Just [product zs])


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

    -- we decided not to introduce special variables for defining sensRows, but use row filters instead
    --let tableSensRows = map (extractRange plcExpr) tableNames in
    let tableSensRows = replicate (length tableNames) [(0 :: Int)..] in

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

