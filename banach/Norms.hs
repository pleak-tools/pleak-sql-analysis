module Norms where

import Data.Graph.MaxBipartiteMatching
import Data.List
import Data.Map
import Data.Tuple
import qualified Data.Set as S
import Debug.Trace

-- import Expr directly from Banach.hs, 'qualified' because we want to reuse the names
import qualified Banach as B

-- this is a double with additional top-value "any", meaning that any double is allowed at this place
data ADouble = AtMost Double | Any
  deriving Show

-- the composite norm w.r.t. which we compute our sensitivities
-- in the norms, we can use expressions as well as variables
data Norm a = Col a                     -- a variable, if it is toplevel, is treated as its norm (which can be arbitrary)
          | LN (Norm a)
          | NormL     ADouble [Norm a]  -- lp-norm
          | NormLInf  [Norm a]          -- linf-norm
          | NormScale Double (Norm a)   -- scaled norm a * N
          | NormZero (Norm a)           -- the same as NormScale with a -> infinity
          | Dummy
  deriving Show

---------------------------------------------------------------------------------------------
-- TODO: norm derivation for 'expr' and 'tableExpr' is being synchronized with B.Expr and B.TableExpr
deriveNorm :: [a] -> B.Expr -> Norm a
deriveNorm colnames expr = 
    case expr of
        B.PowerLN x _      -> NormL (AtMost 1.0) [LN (Col (colnames !! x))]
        B.Power x _        -> NormL (AtMost 1.0) [Col (colnames !! x)]
        B.ComposePower e c -> deriveNorm colnames e
        B.Exp _ x          -> NormL (AtMost 1.0) [Col (colnames !! x)]
        B.ScaleNorm a e    -> NormScale a (deriveNorm colnames e)
        B.ZeroSens e       -> NormZero (deriveNorm colnames e)
        B.L p xs           -> NormL (AtMost p) (Data.List.map (\x -> Col (colnames !! x)) xs)


        -- a bit of normalization to make norm comparison easier: put together all arguments of a p-norm that have norm p
        B.ComposeL p es    -> let es'  = (Data.List.map (deriveNorm colnames) es) in
                              NormL (AtMost p) (groupLNorm p es')

        B.LInf xs          -> NormLInf (Data.List.map (\x -> Col (colnames !! x)) xs)
        B.Prod es          -> NormL (AtMost 1.0) (Data.List.map (deriveNorm colnames) es)
        B.Min es           -> NormL Any (Data.List.map (deriveNorm colnames) es)
        B.Max es           -> NormL Any (Data.List.map (deriveNorm colnames) es)

deriveTableNorm ::  [a] -> B.TableExpr -> Norm a
deriveTableNorm colnames expr = 
    case expr of
        B.SelectProd e     -> NormL (AtMost 1.0) [deriveNorm colnames e]
        B.SelectMin  e     -> NormL Any [deriveNorm colnames e]
        B.SelectMax  e     -> NormL Any [deriveNorm colnames e]
        B.SelectL p  e     -> NormL (AtMost p) [deriveNorm colnames e]

-- TODO check if q <= p and q >= p would be better
-- ||x|_p, |y|_p, z|_p == ||x,y|_p, z|_p
groupLNorm :: Double -> [Norm a] -> [Norm a]
groupLNorm p       [] = []

-- we have reserved the double 10000 for infinity
groupLNorm 10000.0 ns =
     let (ns1,ns2) = Data.List.partition (\x -> (case x of {NormLInf _ -> True; Col y -> True;  _ -> False})) ns in
     let ns1vars = concat (Data.List.map (\x -> (case x of {NormLInf xs -> xs;  Col y -> [Col y]; _ -> error ("This should not happen, something is wrong")})) ns1) in
     if (length ns1vars == 0) then ns2 else (NormLInf ns1vars):ns2

groupLNorm p ns =
     let (ns1,ns2) = Data.List.partition (\x -> (case x of {NormL (AtMost q) _ -> (if q == p then True else False); Col y -> True;  _ -> False})) ns in
     let ns1vars = concat (Data.List.map (\x -> (case x of {NormL (AtMost q) xs -> xs; Col y -> [Col y]; _ -> error ("This should not happen, something is wrong")})) ns1) in
     if (length ns1vars == 0) then ns2 else (NormL (AtMost p) ns1vars):ns2

-- ||x,y|_p, z|_p == ||x|_p, |y|_p, z|_p
ungroupLNorm :: Double -> [Norm a] -> [Norm a]
ungroupLNorm p       [] = []

-- we have reserved the double 10000 for infinity
ungroupLNorm 10000.0 ns =
     let (ns1,ns2) = Data.List.partition (\x -> (case x of {NormLInf _ -> True; Col y -> True;  _ -> False})) ns in
     let ns1vars = concat (Data.List.map (\x -> (case x of {NormLInf xs -> xs;  Col y -> [Col y]; _ -> error ("This should not happen, something is wrong")})) ns1) in
     if (length ns1vars == 0) then ns2 else ns1vars ++ ns2

ungroupLNorm p ns =
     let (ns1,ns2) = Data.List.partition (\x -> (case x of {NormL (AtMost q) _ -> (if q == p then True else False); Col y -> True;  _ -> False})) ns in
     let ns1vars = concat (Data.List.map (\x -> (case x of {NormL (AtMost q) xs -> xs; Col y -> [Col y]; _ -> error ("This should not happen, something is wrong")})) ns1) in
     if (length ns1vars == 0) then ns2 else ns1vars ++ ns2

-- do not put it directly into group/ungroup, use only if everything else failed
allNormPartitions1 :: Ordering -> Double -> [Norm a] -> ([Norm a],[Norm a])
allNormPartitions1 _ _ [] = ([],[])
allNormPartitions1 ord 10000.0 xs@((NormLInf z):_) =
        let (ys1,ys2) = Data.List.partition (\x -> (case x of {NormLInf _ -> True; Col y -> True;  _ -> False})) xs in
        let ys1' = concat (Data.List.map (\x -> (case x of {NormLInf xs -> xs;  Col y -> [Col y]; _ -> error ("This should not happen, something is wrong")})) ys1) in
        let (ys,zs) = allNormPartitions1 ord 10000.0 ys2 in
        if (length ys1' == 0) then (ys,zs) else ((NormLInf ys1'):ys, zs)

allNormPartitions1 ord p xs'@((NormL (AtMost q) z):xs) =
    if (compare q p == ord || compare q p == EQ) then
        let (ys1,ys2) = Data.List.partition (\x -> (case x of {NormL (AtMost q') _ -> (if q == q' then True else False); Col y -> True;  _ -> False})) xs' in
        let ys1' = concat (Data.List.map (\x -> (case x of {NormL (AtMost q) xs -> xs; Col y -> [Col y]; _ -> error ("This should not happen, something is wrong")})) ys1) in
        let (ys,zs) = allNormPartitions1 ord p ys2 in
        ((NormL (AtMost q) ys1'):ys, zs)
    else 
        let (ys,zs) = allNormPartitions1 ord p xs in
        (ys, (NormL (AtMost q) z) : zs)

allNormPartitions1 ord p (x:xs) =
        let (ys,zs) = allNormPartitions1 ord p xs in
        (ys, x:zs)

allNormPartitions :: Ordering -> Double -> [Norm a] -> [Norm a]
allNormPartitions ord 10000.0 xs =
    let (ys,zs) = allNormPartitions1 ord 10000.0 xs in
    if (length ys == 0) then zs else (NormLInf ys):zs

allNormPartitions ord p xs =
    let (ys,zs) = allNormPartitions1 ord p xs in
    if (length ys == 0) then zs else (NormL (AtMost p) ys):zs

allTrue :: [Bool] -> Bool
allTrue xs = Data.List.foldr (&&) True xs

exTrue :: [Bool] -> Bool
exTrue xs = Data.List.foldr (||) False xs

-- TODO: The current implementation may make loops, so we limit the number of recursive calls.
--       The counter is the first parameter, and we increase it only in the function verifyNorms,
--       since only that function may expand the term instead of reducing it.
-- the second argument is our expression analysis norm, the third is the user norm
verifyNorm :: (Show a, Eq a) => Int -> Norm a -> Norm a -> Bool

-- let '10000' be reserved for the infinity norm

-- if there is no certain constructor decomposition, let us just compare the two terms
verifyNorm _ (Col x) (Col y) =
    x == y

-- the norm of a vector of length 1 can be matched to any lp norm
verifyNorm k (NormL (AtMost a1) xs) (NormL (AtMost a2) [y]) = 
    verifyNorms k a1 a2 xs [y]

verifyNorm k (NormL (AtMost a1) [x]) (NormL (AtMost a2) ys) = 
    verifyNorms k a1 a2 [x] ys

verifyNorm k (NormLInf xs) (NormL (AtMost a2) [y]) = 
    verifyNorms k 10000.0 a2 xs [y]

verifyNorm k (NormL (AtMost a1) [x]) (NormLInf ys) = 
    verifyNorms k a1 10000.0 [x] ys

verifyNorm k (Col x) (NormL _ [y]) = 
    verifyNorm k (Col x) y

verifyNorm k (NormL _ [x]) (Col y) = 
    verifyNorm k x (Col y)

-- we have x >= ln(x)
verifyNorm k (LN x) y = 
    verifyNorm k x y

-- if the norm is "Any", we assume that it is as good as LInf
-- TODO  It does not make sense to group/ungroup by 10000 is there is no LInf inside.
--       "Any" gives us more possibilities for grouping, we could make more use of it.
verifyNorm k (NormLInf ns1) (NormLInf ns2) =
        verifyNorms k 10000.0 10000.0 ns1 ns2

verifyNorm k (NormL Any ns1) (NormL Any ns2) =
        verifyNorms k 10000.0 10000.0 ns1 ns2

verifyNorm k (NormLInf ns1) (NormL (AtMost a2) ns2) =
        verifyNorms k 10000.0 a2 ns1 ns2

verifyNorm k (NormL Any ns1) (NormL (AtMost a2) ns2) =
        verifyNorms k 10000.0 a2 ns1 ns2

verifyNorm k (NormL Any ns1) (NormLInf ns2) =
        verifyNorms k 10000.0 10000.0 ns1 ns2

verifyNorm k (NormLInf ns1) (NormL Any ns2) =
        verifyNorms k 10000.0 10000.0 ns1 ns2

verifyNorm k (NormL (AtMost a1) ns1) (NormL (AtMost a2) ns2) =
    if (a1 >= a2) then
        verifyNorms k a1 a2 ns1 ns2
    else False

-- if our analyzer only computes some lp norm for p /= \infty, then it is definitely not suitable for "Any" norm
verifyNorm _ (NormL (AtMost _) _) (NormL Any _) =
    False

-- scaling
verifyNorm k (NormScale a1 n1) (NormScale a2 n2) =
    if (a1 == a2) then
        verifyNorm k n1 n2
    else False

verifyNorm k (NormScale a1 n1) n2 =
    if (a1 <= 1) then
        verifyNorm k n1 n2
    else False

verifyNorm k n1 (NormScale a2 n2) =
    if (a2 >= 1) then
        verifyNorm k n1 n2
    else False

-- this is a base case
verifyNorm _ (NormZero _) _ = True

verifyNorm _ _ _ = False

-- here is the main step proving |x_1,...,x_n|_{px} <= |y_1,...,y_m|_{py} for (py <= px)
-- it tries to prove that there is an injective mapping f such that |x_i| <= |y_f(i)| for all i
verifyNorms :: (Show a, Eq a) => Int -> Double ->  Double -> [Norm a] -> [Norm a] -> Bool
verifyNorms _ pX pY [] nsY = True
verifyNorms _ pX pY nsX [] = False
verifyNorms 10 _ _ _ _     = False -- the limit is reached
verifyNorms k pX pY nsX0 nsY0 =

  -- discard all NormZero entries since we do not need to match them
  let nsX = Data.List.filter (\x -> case x of {NormZero _ -> False; _ -> True}) nsX0 in
  let nsY = Data.List.filter (\x -> case x of {NormZero _ -> False; _ -> True}) nsY0 in

  -- after discarding NormZero, check the base cases again
  if (length nsX == 0) then True else
  if (length nsY == 0) then False else

    -- we label the vertices with integers to define an ordering
    let mapX = (zip [0..length nsX] nsX) in
    let mapY = (zip [0..length nsY] nsY) in

    -- for each nsX element, find all elements in nsY that are not smaller than it (call verifyNorm recursively)
    let ns = [ (x,[y | y <- mapY]) | x <- mapX] in
    let edges = S.fromList (concat $ Data.List.map (\((kx,x),ys) -> Data.List.map (\(ky,_) -> (kx,ky)) (Data.List.filter (\(_,y) -> verifyNorm (k+1) x y) ys)) ns) in

    -- get a bipartite graph of results, find a maximal matching in it
    let mmapY = matching edges in
    let mmapX = fromList $ Data.List.map swap (toList mmapY) in -- the inverse map, which always exists for a matching

    --trace ("\nnsY: " ++ show mapY ++ "\n" ++
    --       "nsX: " ++ show mapX ++ "\n" ++
    --       "Matching: " ++ show mmapX) $

    -- if we could match all elements of nsX, then we are done
    let b = (length mmapX) >= (length nsX) in

    -- the following operation may make the matching easier
    -- however, they may also break the previous matching, so use the next only if the previous has failed
    if (b == True) then True else

        -- if the proof failed, we may try to rearrange the terms
        -- collect only the vertices for which we did not get a matching
        let nsY' = Data.List.map snd (Data.List.filter (\(y,_) -> notMember y mmapY) mapY) in
        let nsX' = Data.List.map snd (Data.List.filter (\(x,_) -> notMember x mmapX) mapX) in

        -- try to group the variables in both lists if possible
        let nsY1 = groupLNorm pY nsY' in
        let nsX1 = groupLNorm pX nsX' in

        let b1 = verifyNorms (k+1) pX pY nsX1 nsY1 in
        --trace ("b1: nsY: " ++ show(nsY) ++ " --> " ++ show(nsY1) ++ "\n    nsX: " ++ show(nsX) ++ " --> " ++ show(nsX1)) $
        if b1 == True then True else

            -- try to ungroup the variables in both lists if possible
            let nsY2 = ungroupLNorm pY nsY' in
            let nsX2 = ungroupLNorm pX nsX' in

            let b2 = verifyNorms (k+1) pX pY nsX2 nsY2 in
            --trace ("b2: nsY: " ++ show(nsY) ++ " --> " ++ show(nsY2) ++ "\n    nsX: " ++ show(nsX) ++ " --> " ++ show(nsX2)) $
            if b2 == True then True else

                -- finally, try to group norms also for all q <= p
                let nsY3 = allNormPartitions GT pY nsY' in
                let nsX3 = allNormPartitions LT pX nsX' in

                let b3 = verifyNorms (k+1) pX pY nsX3 nsY3 in
                --trace ("b3: nsY: " ++ show(nsY) ++ " --> " ++ show(nsY3) ++ "\n    nsX: " ++ show(nsX) ++ " --> " ++ show(nsX3)) $
                b3




