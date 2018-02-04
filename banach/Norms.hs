module Norms where

import qualified Data.IntMap as IntMap
import Data.List
import Data.Map
import Data.Maybe
import Data.Tuple
import qualified Data.Set as S
import qualified Data.IntSet as IntSet
import Debug.Trace

import ToySolver.Combinatorial.BipartiteMatching

-- import Expr directly from Banach.hs, 'qualified' because we want to reuse the names
import qualified Banach as B

-- this is a double with additional top-value "any", meaning that any double is allowed at this place
data ADouble = Exactly Double | Any
  deriving (Show,Ord,Eq)

-- the composite norm w.r.t. which we compute our sensitivities
-- in the norms, we can use expressions as well as variables
data Norm a = Col a                     -- a variable, if it is toplevel, is treated as its norm (which can be arbitrary)
          | NormLN    (Norm a)          -- ln-norm |ln x|
          | NormL     ADouble [Norm a]  -- lp-norm
          | NormScale Double (Norm a)   -- scaled norm a * N
          | NormZero (Norm a)           -- the same as NormScale with a -> infinity
          | Dummy
  deriving (Show,Ord,Eq)

-- we use this value as a flag for subterm grouping function
-- TODO we are actually using only Ungroup, probably we will not need this structure at all
data Grouping = Group | Ungroup

---------------------------------------------------------------------------------------------
-- TODO: deriveNorm, deriveTableNorm, updateExpr, updateTableExpr are being synchronized with B.Expr and B.TableExpr
deriveNorm :: [a] -> B.Expr -> Norm a
deriveNorm colnames expr = 
    case expr of
        B.PowerLN x _      -> NormLN (Col (colnames !! x))
        B.Power x _        -> NormL (Exactly 1.0) [Col (colnames !! x)]
        B.ComposePower e c -> deriveNorm colnames e
        B.Exp _ x          -> NormL (Exactly 1.0) [Col (colnames !! x)]
        B.ComposeExp c e   -> deriveNorm colnames e
        B.Sigmoid _ _ x    -> NormL (Exactly 1.0) [Col (colnames !! x)]
        B.ComposeSigmoid _ _ e -> deriveNorm colnames e
        B.Const a          -> NormZero Dummy
        B.ScaleNorm a e    -> NormScale a (deriveNorm colnames e)
        B.ZeroSens e       -> NormZero (deriveNorm colnames e)
        -- TODO should we use p or dual norm here?
        B.L p xs           -> NormL (Exactly p) (Data.List.map (\x -> Col (colnames !! x)) xs)
        B.ComposeL p es    -> NormL (Exactly p) (Data.List.map (deriveNorm colnames) es)
        B.LInf xs          -> NormL Any (Data.List.map (\x -> Col (colnames !! x)) xs)

        B.Prod es          -> NormL (Exactly 1.0) (Data.List.map (deriveNorm colnames) es)
        B.Prod2 es         -> let subNorms = Data.List.map (deriveNorm colnames) es in
                              Data.List.foldr upperBoundNorm (NormZero Dummy) subNorms
        B.Min es           -> NormL Any (Data.List.map (deriveNorm colnames) es)
        B.Max es           -> NormL Any (Data.List.map (deriveNorm colnames) es)
        B.Sump p es        -> NormL (Exactly p) (Data.List.map (deriveNorm colnames) es)
        B.SumInf es        -> NormL Any (Data.List.map (deriveNorm colnames) es)
        B.Sum2 es          -> let subNorms = Data.List.map (deriveNorm colnames) es in
                              Data.List.foldr upperBoundNorm (NormZero Dummy) subNorms

deriveTableNorm :: B.TableExpr -> ADouble
deriveTableNorm expr = 
    case expr of

        B.SelectProd _     -> Exactly 1.0
        B.SelectMin  _     -> Any
        B.SelectMax  _     -> Any
        B.SelectL p  _     -> Exactly p
        B.SelectSump p _   -> Exactly p
        B.SelectSumInf _   -> Any

-- takes into account modifications in the norm and applies them to the query expression
updateExpr :: Map B.Var Double -> Map B.Var Double -> B.Expr -> B.Expr
updateExpr mapCol mapLN expr =
    case expr of
        B.PowerLN x c      -> B.ScaleNorm (mapLN  ! x) (B.PowerLN x c)
        B.Power x c        -> B.ScaleNorm (mapCol ! x) (B.Power x c)
        B.ComposePower e c -> B.ComposePower (updateExpr mapCol mapLN e) c
        B.Exp c x          -> B.ScaleNorm (mapCol ! x) (B.Exp c x)
        B.ComposeExp c e   -> B.ComposeExp c (updateExpr mapCol mapLN e)
        B.Sigmoid a c x    -> B.ScaleNorm (mapCol ! x) (B.Sigmoid a c x)
        B.ComposeSigmoid a c e -> B.ComposeSigmoid a c (updateExpr mapCol mapLN e)
        -- the constants are currently all below zeroSens, so we do not need a special case for them
        B.ScaleNorm a e    -> updateExpr mapCol mapLN e -- we assume that all scalings have already been taken into account in the maps
        B.ZeroSens e       -> B.ZeroSens e
        B.L p xs           -> B.ScaleNorm (Data.List.foldr min 100000 $ Data.List.map (mapCol !) xs) (B.L p xs)
        B.ComposeL p es    -> B.ComposeL p (Data.List.map (updateExpr mapCol mapLN) es)
        B.LInf xs          -> B.ScaleNorm (Data.List.foldr min 100000 $ Data.List.map (mapCol !) xs) (B.LInf xs)
        B.Prod es          -> B.Prod  (Data.List.map (updateExpr mapCol mapLN) es)
        B.Prod2 es         -> B.Prod2 (Data.List.map (updateExpr mapCol mapLN) es) -- we assume that equality of subnorms has been already checked
        B.Min es           -> B.Min (Data.List.map (updateExpr mapCol mapLN) es)
        B.Max es           -> B.Max (Data.List.map (updateExpr mapCol mapLN) es)
        B.Sump p es        -> B.Sump p (Data.List.map (updateExpr mapCol mapLN) es)
        B.SumInf es        -> B.SumInf (Data.List.map (updateExpr mapCol mapLN) es)
        B.Sum2 es          -> B.Sum2   (Data.List.map (updateExpr mapCol mapLN) es) -- we assume that equality of subnorms has been already checked

updateTableExpr :: B.TableExpr -> Map B.Var Double -> Map B.Var Double -> ADouble -> ADouble -> Int -> B.TableExpr
updateTableExpr expr mapCol mapLN queryAggrNorm dbAggrNorm numOfRows =
    let n = fromIntegral numOfRows in
    let a = scalingLpNorm queryAggrNorm dbAggrNorm n in
    let g = updateExpr mapCol mapLN in
    case expr of
        B.SelectProd es    -> B.SelectProd   $ Data.List.map g $ Data.List.map (B.ScaleNorm a) es
        B.SelectL p  es    -> B.SelectL p    $ Data.List.map g $ Data.List.map (B.ScaleNorm a) es
        B.SelectMin  es    -> B.SelectMin    $ Data.List.map g es
        B.SelectMax  es    -> B.SelectMax    $ Data.List.map g es
        B.SelectSump _ es  -> case dbAggrNorm of
                                  Any       -> B.SelectSumInf $ Data.List.map g es
                                  Exactly p -> B.SelectSump p $ Data.List.map g es
        B.SelectSumInf es  -> B.SelectSumInf $ Data.List.map g es

-- Let p >= q. We have:
-- ||x|_q, |y|_q, z|_p <= ||x,y|_q, z|_p
-- ||x|_p, |y|_p, z|_q <= ||x,y|_p, z|_q
-- these equalities hold for all x,y,z
-- hence, it holds also if we scale some variables by the same value in the terms on both sides

-- find a norm that is an upper bound for both input norms
-- use the inequality |x|_p <= |y|_q for q <= p and |x|_q <= |x,y|_q
upperBoundNorm :: Norm a -> Norm a -> Norm a

-- NormZero is actually the largest, but we assume that the change of sensitive vars is always 0
upperBoundNorm x (NormZero _) = x
upperBoundNorm (NormZero _) y = y

upperBoundNorm (NormL a1 xs) (NormL a2 ys) = NormL (takeCoarser a1 a2) (xs ++ ys)
upperBoundNorm (NormL a1 xs) y = NormL a1 (y : xs)
upperBoundNorm x (NormL a2 ys) = NormL a2 (x : ys)
upperBoundNorm (NormScale a1 x) (NormScale a2 y) = NormScale (max a1 a2) (upperBoundNorm x y)
upperBoundNorm x y = NormL (Exactly 1.0) [x,y]

-- the function groups/ungroups as many subterms are possible
rearrangeNormRec :: Grouping -> Ordering -> ADouble -> [Norm a] -> ([Norm a],[Norm a])
rearrangeNormRec _ _ _ [] = ([],[])

rearrangeNormRec grouping ord (Exactly p) xs'@(x'@(NormL (Exactly q) z):xs) =
    if (compare q p == ord || compare q p == EQ) then
        let (ys1,ys2) = Data.List.partition (\x -> (case x of {NormL (Exactly q') _ -> (if q == q' then True else False); Col y -> True;  _ -> False})) xs' in
        let ys1' = concat (Data.List.map (\x -> (case x of {NormL (Exactly q) xs -> xs; Col y -> [Col y]; _ -> error ("This should not happen, something is wrong")})) ys1) in
        let (ys,zs) = rearrangeNormRec grouping ord (Exactly p) ys2 in
        case grouping of Group -> if (length ys1' == 0) then (ys,zs) else ((NormL (Exactly q) ys1'):ys,zs)
                         Ungroup -> (ys1' ++ ys, zs)
    else 
        let (ys,zs) = rearrangeNormRec grouping ord (Exactly p) xs in
        (ys, x':zs)

-- we have reserved 'Any' for infinity, since in general it allows grouping by any lp-norm 
-- (if we group smaller norms, '=' becomes '<' or '>')
rearrangeNormRec grouping ord Any xs@((NormL Any z):_) =
        let (ys1,ys2) = Data.List.partition (\x -> (case x of {NormL Any _ -> True; Col y -> True;  _ -> False})) xs in
        let ys1' = concat (Data.List.map (\x -> (case x of {NormL Any xs -> xs;  Col y -> [Col y]; _ -> error ("This should not happen, something is wrong")})) ys1) in
        let (ys,zs) = rearrangeNormRec grouping ord Any ys2 in
        case grouping of Group -> if (length ys1' == 0) then (ys,zs) else ((NormL Any ys1'):ys,zs)
                         Ungroup -> (ys1' ++ ys, zs)

rearrangeNormRec grouping LT Any xs@((NormL (Exactly q) z):_) =
        let (ys1,ys2) = Data.List.partition (\x -> (case x of {NormL (Exactly q') _ -> (if q == q' then True else False); Col y -> True;  _ -> False})) xs in
        let ys1' = concat (Data.List.map (\x -> (case x of {NormL (Exactly q) xs -> xs; Col y -> [Col y]; _ -> error ("This should not happen, something is wrong")})) ys1) in
        let (ys,zs) = rearrangeNormRec grouping LT Any ys2 in
        case grouping of Group -> if (length ys1' == 0) then (ys,zs) else ((NormL (Exactly q) ys1'):ys,zs)
                         Ungroup -> (ys1' ++ ys, zs)

rearrangeNormRec grouping ord a (x:xs) =
        let (ys,zs) = rearrangeNormRec grouping ord a xs in
        (ys, x:zs)

rearrangeNorm :: Grouping -> Ordering -> ADouble -> [Norm a] -> [Norm a]
rearrangeNorm grouping ord Any xs =
    let (ys,zs) = rearrangeNormRec grouping ord Any xs in
    case grouping of Group -> if (length ys == 0) then zs else (NormL Any ys):zs
                     Ungroup -> ys ++ zs

rearrangeNorm grouping ord (Exactly p) xs =
    let (ys,zs) = rearrangeNormRec grouping ord (Exactly p) xs in
    case grouping of Group -> if (length ys == 0) then zs else (NormL (Exactly p) ys):zs
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
normalizeNorm :: Ord a => Norm a -> Norm a

-- move all scaling into the brackets as deep as possible
normalizeNorm (NormScale 1.0 x) = normalizeNorm x
normalizeNorm (NormScale c1 (NormScale c2 x)) = normalizeNorm $ NormScale (c1*c2) x
normalizeNorm (NormScale c (NormL a xs))  = normalizeNorm $ NormL a (Data.List.map (\x -> NormScale c x) xs)
normalizeNorm (NormScale c (NormZero x))  = NormZero x
normalizeNorm (NormLN      (NormZero x))  = NormZero x
normalizeNorm (NormL a xs) = 

    -- apply the equality ||x,y|_p, z|_p == ||x|_p, |y|_p, z|_p, normalize the result
    let ys' = Data.List.map normalizeNorm (rearrangeNorm Ungroup EQ a xs) in

    -- if any subnorm repeats, we take it only once
    -- TODO it would be more precise to scale it by sqrt[p](n) for n copies, but current solution is safe anyway
    let ys = S.toList (S.fromList ys') in
    let zs = Data.List.filter (\x -> case x of NormZero _ -> False; _ -> True) ys in
    -- |||x| ||_p = |x|
    case zs of
        [z] -> z
        _   -> NormL a zs

normalizeNorm x = x

-- after the norm has been normalized, we may want to extract all scalings out of it
-- we know how to do it only if scalings are around 'Col x' or 'NormLN (Col x)'
-- hence, a term has to be normalized first
-- there are two mappings: one for 'Col x', another for NormLN (Col x)'
extractScalings :: (Show a, Ord a) => Norm a -> (Map a Double, Map a Double)
extractScalings norm = 
    case norm of
            NormScale a (Col x)          -> (fromList [(x,a)], none)
            NormScale a (NormLN (Col x)) -> (none, fromList [(x,a)])
            Col x                        -> (fromList [(x,1.0)], none)
            NormLN (Col x)               -> (none, fromList [(x,1.0)])
            NormZero x                   -> (none, none)
            -- if the same variable has been used several times, take its minimum scaling
            -- minimum scaling is the one that increases sensitivity the most
            NormL p xs                   -> Data.List.foldr (\(x1,y1) (x2,y2) -> let f = unionWith min in (f x1 x2, f y1 y2)) (none,none) (Data.List.map extractScalings xs)
            x                            -> error ("Cannot extract scaling from: " ++ show x)
    where none = Data.Map.empty

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
    let (scalingMapCol, scalingMapLN) = extractScalings expr in
    let scalings1 = snd $ unzip (toList scalingMapCol) in
    let scalings2 = snd $ unzip (toList scalingMapCol) in
    Data.List.foldr min 100000 (scalings1 ++ scalings2)

-- The number of recursive calls is bounded just for practical safety, there should actually be no loops.
-- The counter is the first parameter, and we increase it only in the function verifyNorms,
--       since only that function may create several branches.
-- The second argument is the expression norm, the third is the database norm.
verifyNorm :: (Show a, Eq a, Ord a) => Int -> Norm a -> Norm a -> Maybe (Norm a)

-- if there is no certain constructor decomposition, let us just compare the two columns
-- we cannot prove x <= y for x /= y, but we can prove x /= x
verifyNorm _ (Col x) (Col y) =
    if x == y then Just (Col x) else Nothing

-- we have x >= ln(x), and ax >= a ln(x) for all a
-- we want to leave scaling out of LN, so we do not use ax >= ln(ax)
verifyNorm k (NormLN x) (NormScale a y) = 
    fmap (\z -> NormScale a (NormLN z)) $ verifyNorm k x y

-- scaling values under LN is bad in any case, let us return Nothing so that other matching could be tried
verifyNorm k (NormLN x) y =
    let v = verifyNorm k x y in
    case v of
        Just (NormScale c w) -> if c == 1.0 then Just (NormLN w) else Nothing
        _ -> fmap NormLN $ v

-- compare lp-norms
-- if the norm is "Any", we treat as LInf
-- First, compare the entire first norm with all args of the second norm
-- (we do not do it the other way around since it would not give additional solutions anyway).
-- If it fails, then go deeper into both norms, applying scaling if necessary
verifyNorm k n1@(Col x) (NormL a2 ns2) =
        fmap head (verifyNorms k a2 a2 [n1] ns2)

verifyNorm k n1@(NormL a1 ns1) (NormL a2 ns2) =
        let ys1 = verifyNorms k a2 a2 [n1] ns2 in
        let vlen = fromIntegral (length ns1) in
        let ys = case ys1 of
                     Just _  -> ys1
                     Nothing -> fmap (Data.List.map (\x -> NormScale (scalingLpNorm a1 a2 vlen) x)) (verifyNorms k Any a2 ns1 ns2)
        in fmap (NormL Any) ys

-- scaling
verifyNorm k (NormScale a1 n1) (NormScale a2 n2) =
    let y = verifyNorm k n1 n2 in
    fmap (\x -> NormScale a2 x) y

verifyNorm k (NormScale a1 n1) n2 =
    verifyNorm k n1 n2

verifyNorm k n1 (NormScale a2 n2) =
    let y = verifyNorm k n1 n2 in
    fmap (\x -> NormScale a2 x) y

-- this is a base case.
-- actually, NormZero is the largest possible norm.
-- however, we have agreed that NormZero in query norm may contain only insensitive variables.
-- hence, the value under NormZero will always be zero in the cases that are interesting to us
verifyNorm _ (NormZero x) _ = Just (NormZero x)
verifyNorm _ _ _ = Nothing

normalizeAndVerify :: (Show a, Eq a, Ord a) => Norm a -> Norm a -> Maybe (Norm a)
normalizeAndVerify n1 n2 = 
    fmap normalizeNorm $ verifyNorm 0 (normalizeNorm n1) (normalizeNorm n2)

-- here is the main step proving |x_1,...,x_n|_{px} <= |y_1,...,y_m|_{py} for (py <= px)
-- it tries to prove that there is an injective mapping f such that |x_i| <= |y_f(i)| for all i
verifyNorms :: (Show a, Eq a, Ord a) => Int -> ADouble ->  ADouble -> [Norm a] -> [Norm a] -> Maybe [Norm a]
verifyNorms _ aX aY [] nsY = Just nsY
verifyNorms _ aX aY nsX [] = Nothing
verifyNorms 10 _ _ _ _     = -- the limit is reached
    trace ("WARNING: reached the limit on recursion depth.") Nothing

verifyNorms k aX aY nsX nsY =

    --this is not needed since the regrouping keeps the terms normalized,
    --but we may need if we use some other kind of regrouping.
    --let nsX = Data.List.map (\x -> normalizeNorm x) nsX0 in
    --let nsY = Data.List.map (\x -> normalizeNorm x) nsY0 in

    -- we label the vertices with integers to define an ordering
    let mapX = zip [0..length nsX] nsX in
    let mapY = zip [0..length nsY] nsY in

    -- for each nsX element, find all elements in nsY that are not smaller than it (call verifyNorm recursively)
    let ns = [ (x,[y | y <- mapY]) | x <- mapX] in
    let edgeLists = Data.List.map (\((kx,x),ys) -> 
                        Data.List.map (\(ky,newx) -> case newx of {Just nx -> ((kx,ky,exprCost nx), nx) })
                            (Data.List.filter (\(_,newx) -> case newx of {Nothing -> False; _ -> True}) 
                                (Data.List.map (\(ky,y) -> (ky,verifyNorm (k+1) x y)) ys)
                            )
                    ) ns
    in

    let allResults = concat edgeLists in
    let edgeMap = fromList (Data.List.map (\((x,y,z),u) -> ((x,y),u)) allResults) in -- this maps edges to the new x that will be used if this edge is taken
    let (edgeList,_) = Data.List.unzip allResults in
    --let edges = S.fromList (edgeList) in

    -- get a bipartite graph of results (edges are the '<=' relations), find a maximal matching in it
    let (_,temp) = maximumWeightMatching (IntSet.fromList [0..length nsX]) (IntSet.fromList [0..length nsY]) edgeList in
    let mlistX = IntMap.toList temp in        -- matching from X to Y
    let mlistY = Data.List.map swap mlistX in -- matching from Y to X
    let mmapY = IntMap.fromList mlistY in
    let mmapX = IntMap.fromList mlistX in

    --trace ("\nnsY: " ++ show mapY ++ "\n" ++
    --       "nsX: " ++ show mapX ++ "\n" ++
    --       "Matching: " ++ show mmapX) $

    -- if we could match all elements of nsX, then we are done
    let b = (length mmapX) >= (length nsX) in
    let matchedSubnorms = Data.List.map (\edge -> edgeMap ! edge) mlistX in

    -- the following operations may make the matching easier
    -- however, they may also break the previous matching, so use the next only if the previous has failed
    if (b == True) then Just matchedSubnorms else

        -- if the proof failed, we may try to rearrange the terms
        -- collect only the vertices for which we did not get a matching
        let nsY' = Data.List.map snd (Data.List.filter (\(y,_) -> IntMap.notMember y mmapY) mapY) in
        let nsX' = Data.List.map snd (Data.List.filter (\(x,_) -> IntMap.notMember x mmapX) mapX) in

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




