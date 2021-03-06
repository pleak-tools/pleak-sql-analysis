module NormsQ where

import Prelude hiding ((!!))
import Data.List hiding ((!!))
import qualified Data.IntMap as IntMap
import qualified Data.Map as M
import Data.Maybe
import Data.Tuple
import qualified Data.Set as S
import qualified Data.IntSet as IntSet
import Debug.Trace

import ToySolver.Combinatorial.BipartiteMatching

-- import Expr directly from Banach.hs, 'qualified' because we want to reuse the names
import qualified Banach as B

import ErrorMsg hiding (at1)
import qualified ErrorMsg as EM (at1)
(!!) xs x = EM.at1 xs x

-- this is a double with additional top-value 'any', meaning that any double is allowed at this place
data ADouble = Exactly Double | Any
  deriving (Show,Ord,Eq)

-- the composite norm w.r.t. which we compute our sensitivities
-- in the norms, we can use expressions as well as variables
data Norm a = Col a                     -- a variable, if it is toplevel, is treated as its norm (which can be arbitrary)
          | NormLN    (Norm a)          -- ln-norm |ln x|; is a norm iff x is a column variable
          | NormLZero (Norm a)          -- l0-norm |x|
          | NormL     ADouble [Norm a]  -- lp-norm
          | NormScale Double (Norm a)   -- scaled norm a * N
          | NormZero                    -- the same as NormScale with a -> infinity
  deriving (Show,Ord,Eq)

niceNorm :: (Show a) => Norm a -> String
niceNorm (Col x) = show x
niceNorm (NormLN z) = if y == "" then "" else "|LN " ++ y ++ "|"
    where y = niceNorm z

niceNorm (NormLZero z) = if y == "" then "" else "|" ++ y ++ "|"
    where y = niceNorm z

niceNorm (NormL (Exactly p) zs) = if y == "" then ""
                                  else if length ys == 1 then y
                                  else  "|" ++ y ++ "|_" ++ show (round p)
    where
        ys = filter (/= "") (map niceNorm zs)
        y = intercalate "," ys

niceNorm (NormL Any zs) = if y == "" then ""
                          else if length ys == 1 then y
                          else  "|" ++ y ++ "|_inf"
    where
        ys = filter (/= "") (map niceNorm zs)
        y = intercalate "," ys

niceNorm (NormScale a z) = if y == "" then "" else (if a == 1.0 then y else show a ++ "* (" ++ y ++ ")")
    where y = niceNorm z

niceNorm NormZero = ""

niceADouble (Exactly p) = show (round p)
niceADouble Any = "inf"


-- default norm variable for automatized norm constructions
-- we assume that noone actually uses this kind of variable
defaultNormVariable = "_nv"

-- we use this value as a flag for subterm grouping function
-- TODO we are actually using only Ungroup, probably we will not need this structure at all
data Grouping = Group | Ungroup

-- Let p >= q. We have:
-- ||x|_q, |y|_q, z|_p <= ||x,y|_q, z|_p
-- ||x|_p, |y|_p, z|_q >= ||x,y|_p, z|_q
-- these equalities hold for all x,y,z
-- hence, it holds also if we scale some variables by the same value in the terms on both sides

-- find a norm that is an upper bound for both input norms
-- use the inequality |x|_p <= |y|_q for q <= p and |x|_q <= |x,y|_q
upperBoundNorm :: Norm a -> Norm a -> Norm a

-- NormZero is actually the largest, but we assume that the change of sensitive vars is always 0
upperBoundNorm x NormZero = x
upperBoundNorm NormZero y = y

upperBoundNorm (NormL a1 xs) (NormL a2 ys) = NormL (takeCoarser a1 a2) (xs ++ ys)
upperBoundNorm (NormL a1 xs) y = NormL a1 (y : xs)
upperBoundNorm x (NormL a2 ys) = NormL a2 (x : ys)
upperBoundNorm (NormScale a1 x) (NormScale a2 y) = NormScale (max a1 a2) (upperBoundNorm x y)
upperBoundNorm x y = NormL (Exactly 1.0) [x,y]

-- the function groups/ungroups as many subterms are possible
rearrangeNormRec :: Grouping -> Ordering -> ADouble -> [Norm a] -> ([Norm a],[Norm a])
rearrangeNormRec _ _ _ [] = ([],[])

-- if we group by non-equal norms, '=' becomes '<' or '>'
-- we have reserved 'Any' for infinity, since in general it allows grouping by any lp-norm 
rearrangeNormRec grouping ord (Exactly p) xs@(x'@(NormL (Exactly q) z):xs') =
    if (compare q p == ord || compare q p == EQ) then
        let (ys1,ys2) = partition (\x -> (case x of {NormL (Exactly q') _ -> (if q == q' then True else False); Col y -> True;  _ -> False})) xs in
        let ys1'    = concat $ map (\x -> (case x of {NormL (Exactly q') vs -> vs; Col y -> [Col y]; _ -> error (error_internal_normRegroup)})) ys1 in
        let (ys,zs) = rearrangeNormRec grouping ord (Exactly p) ys2 in
        case grouping of Group -> if (length ys1' == 0) then (ys,zs) else ((NormL (Exactly q) ys1'):ys,zs)
                         Ungroup -> (ys1' ++ ys, zs)
    else 
        let (ys,zs) = rearrangeNormRec grouping ord (Exactly p) xs' in
        (ys, x':zs)

rearrangeNormRec grouping GT (Exactly p) xs@((NormL Any z):_) =
        let (ys1,ys2) = partition (\x -> (case x of {NormL Any _ -> True; Col y -> True;  _ -> False})) xs in
        let ys1'    = concat $ map (\x -> (case x of {NormL Any vs -> vs;  Col y -> [Col y]; _ -> error (error_internal_normRegroup)})) ys1 in
        let (ys,zs) = rearrangeNormRec grouping GT (Exactly p) ys2 in
        case grouping of Group -> if (length ys1' == 0) then (ys,zs) else ((NormL Any ys1'):ys,zs)
                         Ungroup -> (ys1' ++ ys, zs)

rearrangeNormRec grouping LT Any xs@((NormL (Exactly q) z):_) =
        let (ys1,ys2) = partition (\x -> (case x of {NormL (Exactly q') _ -> (if q == q' then True else False); Col y -> True;  _ -> False})) xs in
        let ys1' = concat $ map (\x -> (case x of {NormL (Exactly q') vs -> vs; Col y -> [Col y]; _ -> error (error_internal_normRegroup)})) ys1 in
        let (ys,zs) = rearrangeNormRec grouping LT Any ys2 in
        case grouping of Group -> if (length ys1' == 0) then (ys,zs) else ((NormL (Exactly q) ys1'):ys,zs)
                         Ungroup -> (ys1' ++ ys, zs)

rearrangeNormRec grouping ord Any xs@((NormL Any z):_) =
        let (ys1,ys2) = partition (\x -> (case x of {NormL Any _ -> True; Col y -> True;  _ -> False})) xs in
        let ys1' = concat $ map (\x -> (case x of {NormL Any vs -> vs;  Col y -> [Col y]; _ -> error (error_internal_normRegroup)})) ys1 in
        let (ys,zs) = rearrangeNormRec grouping ord Any ys2 in
        case grouping of Group -> if (length ys1' == 0) then (ys,zs) else ((NormL Any ys1'):ys,zs)
                         Ungroup -> (ys1' ++ ys, zs)

rearrangeNormRec grouping ord a (x:xs) =
        let (ys,zs) = rearrangeNormRec grouping ord a xs in
        (ys, x:zs)

rearrangeNorm :: Grouping -> Ordering -> ADouble -> [Norm a] -> [Norm a]
rearrangeNorm grouping ord p xs =
    let (ys,zs) = rearrangeNormRec grouping ord p xs in
    case grouping of Group -> if (length ys == 0) then zs else (NormL p ys):zs
                     Ungroup -> ys ++ zs


--TODO we should put this comparison directly into Data ADouble
takeFiner :: ADouble -> ADouble -> ADouble
takeFiner Any         _             = Any
takeFiner _           Any           = Any
takeFiner (Exactly p) (Exactly q)   = Exactly (max p q)

takeCoarser :: ADouble -> ADouble -> ADouble
takeCoarser Any         x             = x
takeCoarser x           Any           = x
takeCoarser (Exactly p) (Exactly q)   = Exactly (min p q)

-- we do some simplifications to make the matching easier
-- 1) Move all scallings deep into the brackets
-- 2) Ungroup variables whenever possible
-- 3) Remove repeating subnorms
normalizeNorm :: Ord a => Norm a -> Norm a

-- move all scaling into the brackets as deep as possible
-- remove scaling by 1.0
normalizeNorm (NormScale 1.0 x) = normalizeNorm x
normalizeNorm (NormScale c1 (NormScale c2 x)) = normalizeNorm $ NormScale (c1*c2) x
normalizeNorm (NormScale c (NormL a xs))  = normalizeNorm $ NormL a $ map (\x -> NormScale c x) xs
normalizeNorm (NormScale c NormZero)  = NormZero
normalizeNorm (NormLN      NormZero)  = NormZero
normalizeNorm (NormLZero   NormZero)  = NormZero
normalizeNorm (NormL p xs) = 


    -- apply the equality ||x,y|_p, z|_p == ||x|_p, |y|_p, z|_p to ungroup, normalize the result
    let ys' = map normalizeNorm $ rearrangeNorm Ungroup EQ p xs in

    -- throw away empty entires that are always 0 anyway
    let ys  = filter (\y -> case y of NormZero -> False; _ -> True) ys' in

    -- if any subnorm repeats, we take it only once using equality |x,x,z|_p = |sqrt[p](2)*x,z|_p
    -- to preserve the equality, we scale a variable by sqrt[p](n) for n copies

    -- count each variable
    let ysUnique = S.toList (S.fromList ys) in
    let counts   = map (\y -> (y, (length . Data.List.filter (==y)) ys)) ysUnique in

    -- scale each variable with the p-th root of its multiplicity
    let rootPow = case p of
            Exactly q -> (1 / q)
            Any       -> 0.0
    in
    let zs' = map (\(y,ny) -> NormScale ((fromIntegral ny) ** rootPow) y) counts in

    -- again, we need to apply normalizeNorm to push the fresh scalings down
    let zs  = map normalizeNorm $ zs' in

    -- we may now get the case |||x| ||_p = |x|
    case zs of
        [z] -> z
        []  -> NormZero
        _   -> NormL p zs

normalizeNorm x = x

-- after the norm has been normalized, we may want to extract all scalings out of it
-- we know how to do it only if scalings are around 'Col x' or 'NormLN (Col x)' or 'NormLZero (Col x)'
-- hence, a term has to be normalized first
-- there are two mappings: one for 'Col x', another for NormLN (Col x)'
-- the function 'aggr' tells what to do with repeating variables
-- the functions 'pre' and 'post' tell how to pre- and and postprocess each variable
extractScalings :: (Show a, Ord a) => (Double -> Double) ->
                                      (Double -> Double -> Double) ->
                                      (Double -> Double) ->
                                      Norm a ->
                                      (M.Map a Double, M.Map a Double, M.Map a Double)
extractScalings pre aggr post norm = 
    let (map1,map2,map3) = extractScalingsRec pre aggr norm in
    (M.map post map1, M.map post map2, M.map post map3)

extractScalingsRec :: (Show a, Ord a) => (Double -> Double) ->
                                         (Double -> Double -> Double) ->
                                         Norm a ->
                                         (M.Map a Double, M.Map a Double, M.Map a Double)
extractScalingsRec pre aggr norm = 
    case norm of
            NormScale a (Col x)             -> (M.fromList [(x,pre a)], none, none)
            NormScale a (NormLN (Col x))    -> (none, M.fromList [(x,pre a)], none)
            NormScale a (NormLZero (Col x)) -> (none, none, M.fromList [(x,pre a)])

            Col x                        -> (M.fromList [(x,pre 1.0)], none, none)
            NormLN (Col x)               -> (none, M.fromList [(x,pre 1.0)], none)
            NormLZero (Col x)            -> (none, none, M.fromList [(x,pre 1.0)])
            -- normZero nullify all scalings since they do not matter anyway
            NormZero                     -> (none, none,none)
            -- if the same variable has been used several times, apply the aggregation to it
            NormL p xs                   -> foldl (\(x1,y1,z1) (x2,y2,z2) -> let f = M.unionWith aggr in (f x1 x2, f y1 y2, f z1 z2)) (none,none,none) $ map (extractScalingsRec pre aggr) xs
            x                            -> error $ error_internal_extractScaling x
    where none = M.empty

-- compares two LP-norms, uses norm equivalence and scales if necessary
scalingLpNorm :: ADouble -> ADouble -> Double -> Double
scalingLpNorm Any Any         _ = 1.0
scalingLpNorm (Exactly _) Any n = n**(-1)
scalingLpNorm Any (Exactly _) _ = 1.0
scalingLpNorm (Exactly p1) (Exactly p2) n =
    if p1 >= p2 then 1.0
    else n**(1/p2 - 1/p1)

-- estmate the cost of an expression: we take the minimum scaling that need to be applied
-- this is safe since the minimum scaling increases sensitivity the most
exprCost :: (Show a, Ord a) => Norm a -> Double
exprCost expr = 
    let (scalingMapCol, scalingMapLN, scalingMapLZero) = extractScalings id min id (normalizeNorm expr) in
    let scalings1 = snd $ unzip (M.toList scalingMapCol) in
    let scalings2 = snd $ unzip (M.toList scalingMapLN) in
    let scalings3 = snd $ unzip (M.toList scalingMapLZero) in
    foldr min 100000 (scalings1 ++ scalings2 ++ scalings3)

-- this is to facilitate different possibilities in the function verfyNorm
tryNext :: (Show a, Eq a, Ord a) => Int -> Double-> Maybe [Norm a] -> ADouble -> ADouble -> ADouble -> ADouble -> [Norm a] -> [Norm a] -> Maybe [Norm a]
tryNext k vlen xs a1 a2 a1' a2' ns1 ns2 =
     case xs of
         Just _  -> xs
         Nothing -> fmap (map (NormScale (scalingLpNorm a1 a2 vlen))) (verifyNorms k a1' a2' ns1 ns2)

-- The number of recursive calls is bounded just for practical safety, there should actually be no loops.
-- The counter is the first parameter, and we increase it only in the function verifyNorms,
--       since only that function may create several branches.
-- The second argument is the expression norm, the third is the database norm.
verifyNorm :: (Show a, Eq a, Ord a) => Int -> Norm a -> Norm a -> Maybe (Norm a)

-- if there is no certain constructor decomposition, let us just compare the two columns
-- we cannot prove x <= y for x /= y, but we can prove x /= x
verifyNorm _ (Col x) (Col y) =
    if x == y then Just (Col x) else Nothing

verifyNorm _ (NormLN (Col x)) (NormLN (Col y)) =
    if x == y then Just (NormLN (Col x)) else Nothing

verifyNorm _ (NormLZero (Col x)) (NormLZero (Col y)) =
    if x == y then Just (NormLZero (Col x)) else Nothing

-- we want to leave scaling out of LN and LZero
verifyNorm k (NormLZero x) (NormScale a y) = 
    fmap (\z -> NormScale a z) $ verifyNorm k (NormLZero x) y

verifyNorm k (NormLN x) (NormScale a y) = 
    fmap (\z -> NormScale a z) $ verifyNorm k (NormLN x) y

-- we have x >= ln(x)
-- scaling values under LN is bad in any case, let us return Nothing so that other matching could be tried
verifyNorm k (NormLN x) y =
    let v = verifyNorm k x y in
    case v of
        Just (NormScale c w) -> if c == 1.0 then Just (NormLN w) else Nothing
        _ -> fmap NormLN $ v

-- compare lp-norms
-- if the norm is 'Any', we treat as LInf
-- First, compare the entire first norm with all args of the second norm
-- (we do not do it the other way around since it would not give additional solutions anyway).
-- If it fails, then go deeper into both norms, applying scaling if necessary
verifyNorm k n1@(Col x) (NormL a2 ns2) =
        fmap head (verifyNorms k a2 a2 [n1] ns2)

verifyNorm k n1@(NormL a1 ns1) (NormL a2 ns2) =

        let a = Exactly 1.0 in
        let vlen1 = fromIntegral (length ns1) in
        let vlen2 = fromIntegral (length ns2) in

        let ys1 = tryNext k vlen2 Nothing a1 a1 a2 a2 [n1] ns2 in -- no scaling needed, we may wrap [n1] with any norm       
        let ys2 = tryNext k vlen2 ys1 a1 a2 a1 a1 [n1] ns2 in -- |y|_a2 = rescale(a1,a2,|y|)^{-1} * |y|_a1, so take rescale(a1,a2,|y|)*|x|_a1
        let ys3 = tryNext k vlen2 ys2 a  a2 a  a  [n1] ns2 in -- |y|_a2 = rescale(a,a2,|y|)^{-1} * |y|_a, so take rescale(1,a2)*|x|_a1 <= rescale(a,a2)*|x|_a

        let ys4 = tryNext k vlen1 ys3 a1 a2 a2 a2 ns1 ns2 in -- |x|_a1 = rescale(a1,a2,|x|)*|x|_a1        
        let ys5 = tryNext k vlen2 ys4 a1 a2 a1 a1 ns1 ns2 in -- |y|_a2 = rescale(a1,a2,|y|)^{-1} * |y|_a1, so take rescale(a1,a2)*|x|_a1
        let ys6 = tryNext k vlen2 ys5 a1 a2 a  a  ns1 ns2 in -- |y|_a2 = rescale(a,a2,|y|)^{-1} * |y|_a, so take rescale(a,a2)*|x|_a1 <= rescale(1,a2)*|x|_a

        case ys6 of 
          Just [] -> Just NormZero
          ys -> fmap (NormL a1) ys

-- scaling
verifyNorm k (NormScale a1 n1) (NormScale a2 n2) =
    let y = verifyNorm k n1 n2 in
    fmap (\x -> NormScale (a2/a1) x) y

verifyNorm k (NormScale a1 n1) n2 =
    let y = verifyNorm k n1 n2 in
    fmap (\x -> NormScale (1/a1) x) y

verifyNorm k n1 (NormScale a2 n2) =
    let y = verifyNorm k n1 n2 in
    fmap (\x -> NormScale a2 x) y

-- this is a base case.
-- actually, NormZero is the largest possible norm.
-- however, we have agreed that NormZero in query norm may contain only insensitive variables.
-- hence, the value under NormZero will always be zero in the cases that are interesting to us
verifyNorm _ NormZero _ = Just NormZero
verifyNorm _ x y = Nothing --trace (show x ++ "\n" ++ show y ++ "\n---") $ Nothing

normalizeAndVerify :: (Show a, Show b, Eq a, Ord a) => (M.Map a b) -> Norm a -> Norm a -> (M.Map a Double, M.Map a Double, M.Map a Double)
normalizeAndVerify invInputMap nx ny =
    -- normalize the norms
    let nnx = normalizeNorm nx in
    let nny = normalizeNorm ny in
    -- first of all, try a more clever norm matching, that may still fail
    let newNorm = fmap normalizeNorm $ verifyNorm 0 nnx nny in
    -- if it does not work, then use a hammer
    case newNorm of
        Just norm -> extractScalings id min id norm
        Nothing   ->
              -- find the finest p-norm in nx and the coarsest norm in ny
              -- we aim to scale variables of nx, so that the norm px will be as large as py
              let px = findMinP nnx in
              let py = findMaxP nny in
              let proot = case py of
                      Exactly q -> (1 / q)
                      Any       -> 0.0
              in

              -- extract scalings of all variables, compute a single scaling sqrt[p](a^p_1 + ... + a^p_k) for repating variables
              let (mapColx, mapLNx, mapLZx) = if proot == 0.0 then extractScalings id max id nnx else extractScalings (\x -> x**(1 / proot)) (+) (\x -> x**proot) nnx in
              let (mapColy, mapLNy, mapLZy) = if proot == 0.0 then extractScalings id max id nny else extractScalings (\x -> x**(1 / proot)) (+) (\x -> x**proot) nny in

              -- scale the variables of nx to match ny, scale with sqrt[p](2) if some variable is used both as x ans lnx in the query
              -- we assume that lzero(x) is not used together with lp(x) and ln(x) since it is categorical vs numerical data
              let scale = 2**(-proot) in
              let listMapCol = map (matchScalings   invInputMap       nnx mapColy)                (M.toList mapColx) in
              let listMapLN  = map (matchLNScalings invInputMap scale nnx mapColx mapColy mapLNy) (M.toList mapLNx)  in
              let listMapLZ  = map (matchLZScalings invInputMap scale nnx mapLZy)                 (M.toList mapLZx)  in

              -- additional scaling is needed in the case px < py
              let n = fromIntegral $ length (listMapCol ++ listMapLN ++ listMapLZ) in
              let a = scalingLpNorm px py n in
              (M.fromList $ map (\(x,xa) -> (x,xa * a)) listMapCol,
               M.fromList $ map (\(x,xa) -> (x,xa * a)) listMapLN,
               M.fromList $ map (\(x,xa) -> (x,xa * a)) listMapLZ)

matchScalings :: (Show a, Show b, Ord a) => (M.Map a b) -> Norm a -> (M.Map a Double) -> (a,Double) -> (a,Double)
matchScalings invInputMap t mapColy (x,a) =
    if M.member x mapColy then
        let b = mapColy ! x in
        (x, (min a b) / a)
    else error $ error_badNorm t (invInputMap ! x)

matchLNScalings :: (Show a, Show b, Ord a) => (M.Map a b) -> Double -> Norm a -> (M.Map a Double) -> (M.Map a Double) -> (M.Map a Double) -> (a,Double) -> (a,Double)
matchLNScalings invInputMap scale t mapColx mapColy mapLNy (x,a) =
    -- if mapLNy also contains x, everything is fine
    if M.member x mapLNy then
        let b = mapLNy ! x in
        (x, (min a b) / a)
    -- we may still take x from mapColy
    else if  M.member x mapColy && not (M.member x mapColx) then
        let b = mapColy ! x in
        (x, (min a b) / a)
    -- we need additional scaling by sqrt[p](2) if mapColx also contained x, to handle two copies
    else if  M.member x mapColy && M.member x mapColx then
        let b = mapColy ! x in
        (x, scale * (min a b) / a)
    else error $ error_badLNNorm t (invInputMap ! x)

matchLZScalings :: (Show a, Show b, Ord a) => (M.Map a b) -> Double -> Norm a -> (M.Map a Double) -> (a,Double) -> (a,Double)
matchLZScalings invInputMap scale t mapLZy (x,a) =
    -- if mapLZy also contains x, everything is fine
    if M.member x mapLZy then
        let b = mapLZy ! x in
        (x, (min a b) / a)
    else error $ error_badLZNorm t (invInputMap ! x)

-- assume that the norm has already been normalized
findMaxP :: Norm a -> ADouble
-- we take the smallest possible value for vectors of length one
findMaxP (Col _)  = Exactly 1.0
findMaxP NormZero = Exactly 1.0
findMaxP (NormLN x) = findMaxP x
findMaxP (NormLZero x) = findMaxP x
findMaxP (NormL Any _) = Any
findMaxP (NormL p xs) = foldl takeFiner p $ map findMaxP xs
findMaxP (NormScale _ x) = findMaxP x

-- assume that the norm has already been normalized
findMinP :: Norm a -> ADouble
-- we take the largest possible value for vectors of length one
findMinP (Col _)  = Any
findMinP NormZero = Any
findMinP (NormLN x) = findMinP x
findMinP (NormLZero x) = findMinP x
findMinP (NormL (Exactly 1.0) xs) = Exactly 1.0
findMinP (NormL p xs) = foldl takeCoarser p $ map findMinP xs
findMinP (NormScale _ x) = findMinP x

-- here is the main step proving |x_1,...,x_n|_{px} <= |y_1,...,y_m|_{py} for (py <= px)
-- it tries to prove that there is an injective mapping f such that |x_i| <= |y_f(i)| for all i
verifyNorms :: (Show a, Eq a, Ord a) => Int -> ADouble ->  ADouble -> [Norm a] -> [Norm a] -> Maybe [Norm a]
verifyNorms _ aX aY [] nsY = Just nsY
verifyNorms _ aX aY nsX [] = Nothing
verifyNorms 10 _ _ _ _     = Nothing -- the limit is reached
   -- trace ("WARNING: reached the limit on recursion depth.") Nothing

verifyNorms k aX aY nsX nsY =

    --this is not needed since the regrouping keeps the terms normalized,
    --but we may need if we use some other kind of regrouping.
    --let nsX = map (\x -> normalizeNorm x) nsX0 in
    --let nsY = map (\x -> normalizeNorm x) nsY0 in

    -- we label the vertices with integers to define an ordering
    let mapX = zip [0..length nsX] nsX in
    let mapY = zip [0..length nsY] nsY in

    -- for each nsX element, find all elements in nsY that are not smaller than it (call verifyNorm recursively)
    let ns = [ (x,[y | y <- mapY]) | x <- mapX] in
    let edgeLists = map (\((kx,x),ys) -> 
                        map (\(ky,newx) -> case newx of {Just nx -> ((kx,ky,exprCost nx), nx) })
                            (filter (\(_,newx) -> case newx of {Nothing -> False; _ -> True}) 
                                (map (\(ky,y) -> (ky,verifyNorm (k+1) x y)) ys)
                            )
                    ) ns
    in

    let allResults = concat edgeLists in
    let edgeMap = M.fromList $ map (\((x,y,z),u) -> ((x,y),u)) allResults in -- this maps edges to the new x that will be used if this edge is taken
    let (edgeList,_) = unzip allResults in
    --let edges = S.fromList (edgeList) in

    -- get a bipartite graph of results (edges are the '<=' relations), find a maximal matching in it
    let (_,temp) = maximumWeightMatching (IntSet.fromList [0..length nsX]) (IntSet.fromList [0..length nsY]) edgeList in
    let mlistX = IntMap.toList temp in        -- matching from X to Y
    let mlistY = map swap mlistX in -- matching from Y to X
    let mmapY = IntMap.fromList mlistY in
    let mmapX = IntMap.fromList mlistX in

    --trace ("\nnsY: " ++ show mapY ++ "\n" ++
    --       "nsX: " ++ show mapX ++ "\n" ++
    --       "Matching: " ++ show mmapX) $

    -- if we could match all elements of nsX, then we are done
    let b = (length mmapX) >= (length nsX) in
    let matchedSubnorms = map (\edge -> edgeMap ! edge) mlistX in

    -- the following operations may make the matching easier
    -- however, they may also break the previous matching, so use the next only if the previous has failed
    if (b == True) then Just matchedSubnorms else

        -- if the proof failed, we may try to rearrange the terms
        -- collect only the vertices for which we did not get a matching
        let nsY' = map snd $ filter (\(y,_) -> IntMap.notMember y mmapY) mapY in
        let nsX' = map snd $ filter (\(x,_) -> IntMap.notMember x mmapX) mapX in

        -- try to ungroup the subterms: nsX by aX, nsY by aY, still having "="
        let nsY1 = rearrangeNorm Ungroup LT aY nsY' in
        let nsX1 = rearrangeNorm Ungroup GT aX nsX' in

        let newx1 = if (length nsY1 == length nsY') && (length nsX1 == length nsX') then Nothing else verifyNorms (k+1) aX aY nsX1 nsY1 in
        let b1 = case newx1 of {Nothing -> False; _ -> True} in
        --trace ("b1: nsY: " ++ show(nsY) ++ " --> " ++ show(nsY1) ++ "\n    nsX: " ++ show(nsX) ++ " --> " ++ show(nsX1)) $
        if b1 == True then fmap (matchedSubnorms ++) newx1 else

            -- try to ungroup the subterms: nsX,nsY by aX, getting ">=" for nsY
            let nsY2 = rearrangeNorm Ungroup LT aX nsY' in
            let nsX2 = rearrangeNorm Ungroup GT aX nsX' in

            let newx2 = if (length nsY2 == length nsY') && (length nsX2 == length nsX') then Nothing else verifyNorms (k+1) aX aX nsX2 nsY2 in
            let b2 = case newx2 of {Nothing -> False; _ -> True} in
            --trace ("b2: nsY: " ++ show(nsY) ++ " --> " ++ show(nsY2) ++ "\n    nsX: " ++ show(nsX) ++ " --> " ++ show(nsX2)) $
            if b2 == True then fmap (matchedSubnorms ++) newx2 else

                -- try to ungroup the subterms: nsX,nsY by aY, getting "<=" for nsX
                let nsY3 = rearrangeNorm Ungroup LT aY nsY' in
                let nsX3 = rearrangeNorm Ungroup GT aY nsX' in

                let newx3 = if (length nsY3 == length nsY') && (length nsX3 == length nsX') then Nothing else verifyNorms (k+1) aY aY nsX3 nsY3 in

                let b3 = case newx3 of {Nothing -> False; _ -> True} in
                --trace ("b3: nsY: " ++ show(nsY) ++ " --> " ++ show(nsY3) ++ "\n    nsX: " ++ show(nsX) ++ " --> " ++ show(nsX3)) $
                fmap (matchedSubnorms ++) newx3




