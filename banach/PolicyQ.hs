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

-------------------------------
---- policy data structures ----
-------------------------------

data VarState
  = Exact | None | Approx Double
  | IntSubSet   [Int]              | SubSet   [String]              | Range   Double Double                | Total Int
  | IntSubSetUn [Int]              | SubSetUn [String]              | RangeUn Double Double                | TotalUn Int
  | IntSubSetPr (M.Map Int Double) | SubSetPr (M.Map String Double) | RangePr Double (M.Map Double Double)
  deriving (Show)

type PlcExpr     = AExpr (String, VarState)
type PlcCostType = (PlcExpr,Double,[(String, AExpr VarName)])

getStatement (plcExpr,_,_) = plcExpr
getCost (_,cost,_) = cost
getFilters (_,_,fs) = fs

niceNormPrint :: (Show a) => Norm a -> String
niceNormPrint = niceNorm

niceADoublePrint :: ADouble -> String
niceADoublePrint = niceADouble

getUb :: Double -> M.Map Double Double -> Double
getUb lb mp = foldr max lb (M.keys mp)

-- traverse the boolean formula
-- apply the function fvar to a variable and fconst to a constant
-- combine the results using the functions fand and for
traverseExpr :: (a -> a -> a) -> (a -> a -> a) -> (Double -> a) -> (b -> String -> a) -> (AExpr (String,b)) -> a
traverseExpr _ _ fconst fvar (AVar (varName,varState)) =
    fvar varState varName

traverseExpr _ _ fconst fvar (AConst x) =
    fconst x

traverseExpr fand for fconst fvar (ABinary AAnd x1 x2) =
    let y1 = traverseExpr fand for fconst fvar x1 in
    let y2 = traverseExpr fand for fconst fvar x2 in
    fand y1 y2

traverseExpr fand for fconst fvar (ABinary AOr x1 x2) =
    let y1 = traverseExpr fand for fconst fvar x1 in
    let y2 = traverseExpr fand for fconst fvar x2 in
    for y1 y2


-- verify the "goodness" of attacker an policy states
isBadPlcState :: String -> VarState -> (Bool,String)
isBadPlcState var x =
    case x of
            Exact -> (False,"")
            None  -> (False,"")
            Range _ _   -> (True, err_badPolicy x)
            IntSubSet _ -> (True, err_badPolicy x)
            Approx r -> if r >= 0 then (False,"") else (True, err_badPolicy_r x)
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
isLeakedVar :: VarState -> VarState -> Bool
isLeakedVar attState plcState =
    case (attState, plcState) of

            (Exact,_)  -> True
            (None, _)  -> False
            (_, Exact) -> False
            (_, None)  -> False

            -- here we assume that the actual data belongs to (lb,ub) -- i.e. the attacker knowledge is correct
            -- while (ub - lb) / 2 <= r2 would already be sufficient in the case when the actual data is in the middle,
            -- we only claim immediate leakage if it leaks for sure
            (Range   lb ub,  Approx r) -> (ub - lb) <= r
            (RangeUn lb ub,  Approx r) -> (ub - lb) <= r
            (RangePr lb ubs, Approx r) -> (sum $ map (\ub -> if ub - lb <= r then ubs ! ub else 0) (M.keys ubs)) == 1

            _ -> error $ error_badAttackerPolicyCombination attState plcState


-- the variable is not sensitive either if attacker already knows it, or we do not care about it
isSensVar :: VarState -> VarState -> Bool
isSensVar attState plcState =
    if isLeakedVar attState plcState then False
    else case (attState, plcState) of
            (_, None) -> False
            _         -> True

-- TODO it seems that we should distinguish AND and OR, since a complete leakage in an AND can still be bearable
verifyVarsSecrecy :: M.Map String VarState -> M.Map String Double -> PlcExpr -> [(String, (Int, [Bool],[VarName],[Expr]))]
verifyVarsSecrecy attMap scaleMap plcExpr =
    traverseExpr (++) (++) (const []) (\x y -> [verifyVarSecrecy attMap scaleMap x y]) plcExpr

verifyVarSecrecy :: M.Map String VarState -> M.Map String Double -> VarState -> String -> (String, (Int, [Bool],[VarName],[Expr]))
verifyVarSecrecy attMap scaleMap plcState preficedVar =

    let [prefix,var] = case (varNameToTableAndSubVarName preficedVar) of
                           [s1,s2] -> [s1,s2]
                           _       -> error $ error_badPolicyFormat preficedVar
    in

    let attState = if M.member preficedVar attMap then attMap ! preficedVar else None in

    let leakedVar = [isLeakedVar attState plcState] in
    let sensVar = if isSensVar attState plcState then [var] else [] in

    -- constuct the norm, which is NormZero for insensitive vars, L0 for exact guesses, and is abs.value for approximated guesses
    let normVar = case (attState, plcState) of
            (Exact,_)    -> []
            (_, None)    -> []
            (_,Exact)    -> [LZero var]
            (_,Approx _) -> let r = scaleMap ! preficedVar in [ScaleNorm (1/r) var]
            _ -> error $ error_badAttackerPolicyCombination attState plcState
    in

    (prefix, (1, leakedVar,sensVar,normVar))

-- extract variable names
extract_vars :: PlcExpr-> [String]
extract_vars plcExpr =
    traverseExpr (++) (++) (const []) (\x y -> [y]) plcExpr

-- extract variable states
extract_states :: PlcExpr-> [VarState]
extract_states plcExpr =
    traverseExpr (++) (++) (const []) (\x y -> [x]) plcExpr

-- check whether sensitivity w.r.t. that variable needs to be analysed at all
extract_bs :: M.Map String VarState -> PlcExpr -> [Bool]
extract_bs attMap plcExpr =
    traverseExpr (++) (++) (const []) (\x y -> [extract_b attMap x y]) plcExpr

extract_b :: M.Map String VarState -> VarState -> String -> Bool
extract_b attMap plcState var =
    let attState = if M.member var attMap then attMap ! var else None in
    isSensVar attState plcState

-- extract the guessing radius
extract_rs :: M.Map String VarState -> PlcExpr -> [Double]
extract_rs attMap plcExpr =
    traverseExpr (++) (++) (const []) (\x y -> [extract_r attMap x y]) plcExpr

extract_r :: M.Map String VarState -> VarState -> String -> Double
extract_r attMap plcState var =
    let attState = if M.member var attMap then attMap ! var else None in
    case (attState, plcState) of
            (_,Exact)    -> 1.0 -- compatible with L0-norm
            (_,Approx r) -> r
            _ -> error $ error_badAttackerPolicyCombination attState plcState

-- extract whether the dimension has discrete norm
extract_ds :: M.Map String VarState -> PlcExpr -> [Bool]
extract_ds attMap plcExpr =
    traverseExpr (++) (++) (const []) (\x y -> [extract_d attMap x y]) plcExpr

extract_d :: M.Map String VarState -> VarState -> String -> Bool
extract_d attMap plcState var =
    let attState = if M.member var attMap then attMap ! var else None in
    case (attState, plcState) of
            (_,Exact)    -> True
            (_,Approx r) -> False
            _ -> error $ error_badAttackerPolicyCombination attState plcState

-- extract the function computing probabilities in total space
extract_gs :: M.Map String VarState -> PlcExpr -> [Double -> Maybe [Double]]
extract_gs attMap plcExpr =
    traverseExpr (++) (++) (const []) (\x y -> [extract_g attMap x y]) plcExpr

extract_g :: M.Map String VarState -> VarState -> String -> (Double -> Maybe [Double])
extract_g attMap plcState var =
    let attState = if M.member var attMap then attMap ! var else None in
    case (attState, plcState) of
            (Exact,_)        -> const $ Just [1.0]     -- the sensitive region already has sensitivity 1
            (None, _)        -> const Nothing        -- no knowledge

            -- unknown distribution
            (Total n, _)     -> const Nothing
            (SubSet xs,_)    -> const Nothing
            (IntSubSet xs,_) -> const Nothing
            (Range lb ub,_)  -> const Nothing

            -- uniform distribution
            -- since the distance does not depend on x, it always makes sense to take the entire space for a > 1
            (TotalUn n, _)     -> (\x -> if x == 1 then Just [1 / fromIntegral n] else Just [1.0])
            (SubSetUn xs,_)    -> let n = length xs in (\x -> if x == 1 then Just [1 / fromIntegral n] else Just [1.0])
            (IntSubSetUn xs,_) -> let n = length xs in (\x -> if x == 1 then Just [1 / fromIntegral n] else Just [1.0])
            -- here the distance does depend on x
            (RangeUn lb ub,_)  -> let rr = (ub - lb) / 2.0 in (\x -> Just [x / rr])

            -- customized distribution
            -- we look at all possiblilities for "g 1", and take "g a = 1" for a > 1
            (SubSetPr mp,_)    -> (\x -> if x == 1 then Just (M.elems mp) else Just (replicate (M.size mp) 1.0))
            (IntSubSetPr mp,_) -> (\x -> if x == 1 then Just (M.elems mp) else Just (replicate (M.size mp) 1.0))

            -- if the range is given in several segments, we assume that the distribution inside each segment is uniform
            -- TODO can we do something better?
            (RangePr lb mp,_)  -> (\x ->
                                       -- compute the weight of blocks that are fully under x
                                       let p1 = sum $ map (\ub -> if ub - lb <= x then mp ! ub else 0) (M.keys mp) in
                                       -- compute the partial weight of the block where x locates
                                       let ubsL = takeWhile (<= x) (M.keys mp) in
                                       let ubsR = dropWhile (<  x) (M.keys mp) in
                                       let ubL = if length ubsL > 0 then last ubsL else lb in
                                       let ubR = if length ubsR > 0 then head ubsR else getUb lb mp in
                                       let p2 = if ubL == ubR then 0 else ((x + lb) - ubL) / (ubR - ubL) * (mp ! ubR) in
                                       Just [p1 + p2])

            _ -> error $ error_badAttackerPolicyCombination attState plcState

-- extract the total space radius
extract_Rs :: M.Map String VarState -> M.Map String String -> PlcExpr -> [Double]
extract_Rs attMap typeMap plcExpr =
    traverseExpr (++) (++) (const []) (\x y -> [extract_R attMap typeMap x y]) plcExpr

extract_R :: M.Map String VarState -> M.Map String String -> VarState -> String -> Double
extract_R attMap typeMap plcState var =
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
            _ -> error $ error_badAttackerPolicyCombination attState plcState


{-
extractRange plcExpr tableName =
    let key = preficedVarName tableName reservedSensRowsKeyword in
    S.toList $ traverseExpr (S.union) (S.union) (const (S.empty)) (extractRanges key) plcExpr

extractRanges key varState var =
    if key == var then
        case varState of
                Range lb ub    -> S.fromList [round lb .. round (ub-1)]
                RangePr lb mp  -> let ub = getUb lb mp in S.fromList [round lb .. round (ub-1)]
                IntSubSet xs   -> S.fromList xs
                IntSubSetPr mp -> S.fromList (M.keys mp)
                _            -> error $ error_badPolicySensRows varState
    else
        S.empty
-}

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

-- construct the norm w.r.t. which we compute sensitivity (used only for the output; this is the 'database norm' that should be understandable to the user)
-- TODO should we apply bss filter, or leave everything as it is?
deriveDbNorm :: M.Map String VarState -> PlcExpr -> Norm String
deriveDbNorm attMap plcExpr =

    -- we put together all variables of all sensitive sets to define one norm over all of them
    let bs  = extract_bs attMap plcExpr in
    let xs  = filterWith bs $ extract_vars   plcExpr in
    let ds  = filterWith bs $ extract_ds attMap plcExpr in
    let rs  = filterWith bs $ extract_rs attMap plcExpr in

    -- if the same variable repeats with different precisions, we agree that we scale the space by the minimum to keep r <= 1
    let scaleMap =  M.fromListWith (\(d,r1) (_,r2) -> (d, max r1 r2)) $ zip xs (zip ds rs) in
    let ys  = map (\(x, (d,r)) -> if d then NormLZero (Col x) else NormScale (1/r) (Col x)) (M.toList scaleMap) in
    NormL (Exactly 1.0) ys

-- construct the norm w.r.t. which we compute sensitivity -- the construction that we actually use in the analysis, with optimizations
constructNormData :: [TableName] -> M.Map String VarState -> PlcExpr -> [(([Int], [VarName]), NormFunction, Maybe Double)]
constructNormData tableNames attMap plcExpr =

    -- TODO remove the special variables that are not needed
    --let kwlen = length reservedSensRowsKeyword in
    --let plcMapData = map (M.filterWithKey (\varName _ -> length varName < kwlen || reverse (take kwlen (reverse varName)) /= reservedSensRowsKeyword) . fst) plcMaps in

    -- check that the attacker knowledge and the sensitive variables have been defined correctly
    let badAttStates = map isBadAttState $ M.elems attMap in

    let plcMapVars   = extract_vars   plcExpr in
    let plcMapStates = extract_states plcExpr in

    let badPlcStates = zipWith isBadPlcState plcMapVars plcMapStates in
    let badStates = badAttStates ++ badPlcStates in
    let (somethingBad,errorMessages) = foldr (\(b1,e1) (b2,e2) -> (b1 || b2, if e1 == "" then e2 else e1 ++ ";\n" ++ e2)) (False,"") badStates in
    if somethingBad then error errorMessages else

    -- we put together all variables of all sensitive sets to define one norm over all of them
    let bs  = extract_bs attMap plcExpr in
    let xs  = filterWith bs $ plcMapVars in
    let ds  = filterWith bs $ extract_ds attMap plcExpr in
    let rs  = filterWith bs $ extract_rs attMap plcExpr in

    -- if the same variable repeats with different precisions, we agree that we scale the space by the minimum to keep r <= 1
    let scaleMap' = M.fromListWith (\(d,r1) (_,r2) -> if d then (d,1.0) else (d,max r1 r2)) $ zip xs (zip ds rs) in
    let scaleMap  = M.map snd scaleMap' in

    let combinedDataMap = constructNormDataSet tableNames attMap scaleMap plcExpr in

    -- we decided not to introduce special variables for defining sensRows, but use row filters instead
    --let tableSensRows = map (extractRange plcExpr) tableNames in
    let tableSensRows = replicate (length tableNames) [(0 :: Int)..] in

    zipWith (normsFromCombinedData combinedDataMap) tableNames tableSensRows


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

constructNormDataSet :: [TableName] -> M.Map String VarState -> M.Map String Double -> PlcExpr -> M.Map TableName (M.Map String Expr)
constructNormDataSet tableNames attMap scaleMap plcExpr =

    -- aggregate the variables for each table separately
    let dataMap = M.fromListWith (\(n1,x1s,y1s,z1s) (n2,x2s,y2s,z2s) -> (n1 + n2, x1s ++ x2s, y1s ++ y2s, z1s ++ z2s)) $ verifyVarsSecrecy attMap scaleMap plcExpr in

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

