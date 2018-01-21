module Norms where

import Data.List
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


-- TODO here are some rewriting rules that we are able to apply, we could improve the search
-- the first argument is our expression analysis norm, the second is the user norm
verifyNorm :: (Show a, Eq a) => Norm a -> Norm a -> Bool

-- let '10000' be reserved for the infinity norm

-- if there is no certain constructor decomposition, let us just compare the two terms
verifyNorm (Col x) (Col y) =
    x == y

-- the norm of a vector of length 1 can be matched to any lp norm
verifyNorm (NormL (AtMost a1) xs) (NormL (AtMost a2) [y]) = 
    verifyNorms a1 a2 xs [y]

verifyNorm (NormL (AtMost a1) [x]) (NormL (AtMost a2) ys) = 
    verifyNorms a1 a2 [x] ys

verifyNorm (NormLInf xs) (NormL (AtMost a2) [y]) = 
    verifyNorms 10000.0 a2 xs [y]

verifyNorm (NormL (AtMost a1) [x]) (NormLInf ys) = 
    verifyNorms a1 10000.0 [x] ys

verifyNorm (Col x) (NormL _ [y]) = 
    verifyNorm (Col x) y

verifyNorm (NormL _ [x]) (Col y) = 
    verifyNorm x (Col y)

-- we have x >= ln(x)
verifyNorm (LN x) y = 
    verifyNorm x y

-- if the norm is "Any", we assume that it is as good as LInf
-- TODO  It does not make sense to group/ungroup by 10000 is there is no LInf inside.
--       "Any" gives us more possibilities for grouping, we could make more use of it.
verifyNorm (NormLInf ns1) (NormLInf ns2) =
        verifyNorms 10000.0 10000.0 ns1 ns2

verifyNorm (NormL Any ns1) (NormL Any ns2) =
        verifyNorms 10000.0 10000.0 ns1 ns2

verifyNorm (NormLInf ns1) (NormL (AtMost a2) ns2) =
        verifyNorms 10000.0 a2 ns1 ns2

verifyNorm (NormL Any ns1) (NormL (AtMost a2) ns2) =
        verifyNorms 10000.0 a2 ns1 ns2

verifyNorm (NormL Any ns1) (NormLInf ns2) =
        verifyNorms 10000.0 10000.0 ns1 ns2

verifyNorm (NormLInf ns1) (NormL Any ns2) =
        verifyNorms 10000.0 10000.0 ns1 ns2

verifyNorm (NormL (AtMost a1) ns1) (NormL (AtMost a2) ns2) =
    if (a1 >= a2) then
        verifyNorms a1 a2 ns1 ns2
    else False

-- if our analyzer only computes some lp norm for p /= \infty, then it is definitely not suitable for "Any" norm
verifyNorm (NormL (AtMost _) _) (NormL Any _) =
    False

-- scaling
verifyNorm (NormScale a1 n1) (NormScale a2 n2) =
    if (a1 == a2) then
        verifyNorm n1 n2
    else False

verifyNorm (NormScale a1 n1) n2 =
    if (a1 <= 1) then
        verifyNorm n1 n2
    else False

verifyNorm n1 (NormScale a2 n2) =
    if (a2 >= 1) then
        verifyNorm n1 n2
    else False

-- this is a base case
verifyNorm (NormZero _) _ = True

verifyNorm _ _ = False

-- here is the main step proving |x_1,...,x_n|_{px} <= |y_1,...,y_m|_{py} for (py <= px)
-- it tries to prove \forall x_i \exists y_i: x_i <= y_i, such that all y_i are distinct
verifyNorms :: (Show a, Eq a) => Double ->  Double -> [Norm a] -> [Norm a] -> Bool
verifyNorms pX pY [] nsY = True
verifyNorms pX pY nsX [] = False
verifyNorms pX pY nsX0 nsY0 =

  -- discard all NormZero entries since we do not need to match them
  let nsX = Data.List.filter (\x -> case x of {NormZero _ -> False; _ -> True}) nsX0 in
  let nsY = Data.List.filter (\x -> case x of {NormZero _ -> False; _ -> True}) nsY0 in

  -- TODO this should skip only the first branch, not immediately fail
  if (length nsX > length nsY) then False
  else

    -- for each nsX element, find all elements in nsY that are not smaller than it
    -- get a binary matrix of results
    let ns = [ (x,[y | y <- nsY]) | x <- nsX] in
    let bss1 = Data.List.map (\(x,ys) -> Data.List.map (verifyNorm x) ys) ns in

    -- check if it is possible to assign a unique y_i to each x_i by counting non-zero columns
    let bss2 = (Data.List.transpose bss1) in
    let bs2  = Data.List.filter exTrue bss2 in
    let b = (length bs2) >= (length nsX) in

    --trace (show(nsY) ++ "\n" ++ show(nsX) ++ "\n" ++ show(p) ++ "\n" ++ show(b)) (if b == True then True
    if b == True then True else

        -- if the proof failed, we may try to rearrange the terms
        -- collect the norms for which we did not get a matching
        let nsY' = Data.List.map (\(x,y) -> y) (Data.List.filter (\(x,y) -> not (exTrue x)) (zipWith (\x y -> (x,y)) bss2 nsY)) in
        let nsX' = Data.List.map (\(x,y) -> y) (Data.List.filter (\(x,y) -> not (exTrue x)) (zipWith (\x y -> (x,y)) bss1 nsX)) in

        -- try to group   the variables in both norms if possible
        -- this operation may make the matching easier
        let nsY1 = groupLNorm pY nsY' in
        let nsX1 = groupLNorm pX nsX' in

        -- check if we now have strictly less elements, so that this would not create infinite loops
        if (length nsX == length nsX1) && (length nsY == length nsY1) then False else 
        let b1 = verifyNorms pX pY nsX1 nsY1 in
        if b1 == True then True else
            -- try to ungroup the variables in both norms if possible
            -- this operation may make the matching easier
            let nsY2 = ungroupLNorm pY nsY' in
            let nsX2 = ungroupLNorm pX nsX' in

            -- check if we now have strictly less elements, so that this would not create infinite loops
            if (length nsX == length nsX2) && (length nsY == length nsY2) then False else 
            let b2 = verifyNorms pX pY nsX2 nsY2 in

            --trace (show(nsY) ++ "\n" ++ show(nsY2) ++ "\n" ++ show(nsX) ++ "\n" ++ show(nsX2) ++ "\n" ++ show(b2) ++ "\n") b2)
            if b2 == True then True else

                -- finally, try to group norms also for all q <= p
                -- this operation may make the matching easier
                let nsY3 = allNormPartitions GT pY nsY' in
                let nsX3 = allNormPartitions LT pX nsX' in

                -- check if we now have strictly less elements, so that this would not create infinite loops
                if (length nsX == length nsX3) && (length nsY == length nsY3) then False else
                let b3 = verifyNorms pX pY nsX3 nsY3 in
                trace ("==> " ++ show(nsY) ++ "\n" ++ show(nsY3) ++ "\n" ++ show(nsX) ++ "\n" ++ show(nsX3) ++ "\n" ++ show(b3) ++ "\n") b3




