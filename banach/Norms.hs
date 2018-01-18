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
data Norm a = Col a               -- a variable, if it is toplevel, it is meant to be the absolute value
          | NormL     ADouble [Norm a]  -- lp-norm
          | NormLInf  [Norm a]          -- linf-norm
          | NormScale Double (Norm a)   -- scaled norm a * N
          | NormZero                    -- the same as NormScale with a -> infinity
  deriving Show

---------------------------------------------------------------------------------------------
-- TODO: norm derivation for 'expr' and 'tableExpr' is being synchronized with B.Expr and B.TableExpr
deriveNorm :: [a] -> B.Expr -> Norm a
deriveNorm colnames expr = 
    case expr of
        B.Power x _        -> NormL (AtMost 1.0) [Col (colnames !! x)]
        B.ComposePower e c -> deriveNorm colnames e
        B.Exp _ x          -> NormL (AtMost 1.0) [Col (colnames !! x)]
        B.ScaleNorm a e    -> NormScale a (deriveNorm colnames e)
        B.ZeroSens _       -> NormZero
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

-- ||x|_p, |y|_p, z|_p == ||x,y|_p, z|_p
groupLNorm :: Double -> [Norm a] -> [Norm a]
groupLNorm p       [] = []

-- we have reserved the double 10000 for infinity
groupLNorm 10000.0 ns =
     let ns1 = Data.List.filter (\x -> (case x of {NormLInf _ -> True;  _ -> False})) ns in
     let ns2 = Data.List.filter (\x -> (case x of {NormLInf _ -> False; _ -> True })) ns in
     let ns1vars = concat (Data.List.map (\x -> (case x of {NormLInf xs -> xs; Col y -> [Col y]; _ -> error ("This should not happen, something is wrong")})) ns1) in
     if (length ns1vars == 0) then ns2 else (NormLInf ns1vars):ns2

groupLNorm p ns =
     let ns1 = Data.List.filter (\x -> (case x of {NormL (AtMost q) _ -> (if q == p then True else False); Col y -> if p == 1.0 then True  else False; _ -> False})) ns in
     let ns2 = Data.List.filter (\x -> (case x of {NormL (AtMost q) _ -> (if q == p then False else True); Col y -> if p == 1.0 then False else True;  _ -> True })) ns in
     let ns1vars = concat (Data.List.map (\x -> (case x of {NormL (AtMost q) xs -> xs; Col y -> [Col y]; _ -> error ("This should not happen, something is wrong")})) ns1) in
     if (length ns1vars == 0) then ns2 else (NormL (AtMost p) ns1vars):ns2


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
verifyNorm (NormL (AtMost a1) xs) (NormL _ [y]) = 
    verifyNorms a1 xs [y]

verifyNorm (NormL _ [x]) (NormL (AtMost a2) ys) = 
    verifyNorms a2 [x] ys

verifyNorm (NormLInf xs) (NormL _ [y]) = 
    verifyNorms 10000.0 xs [y]

verifyNorm (NormL _ [x]) (NormLInf ys) = 
    verifyNorms 10000.0 [x] ys

verifyNorm (Col x) (NormL _ [y]) = 
    verifyNorm (Col x) y

verifyNorm (NormL _ [x]) (Col y) = 
    verifyNorm x (Col y)

-- if the norm is "Any", we assume that it is as good as LInf
verifyNorm (NormLInf ns1) (NormLInf ns2) =
        verifyNorms 10000.0 ns1 ns2

verifyNorm (NormL Any ns1) (NormL Any ns2) =
        verifyNorms 10000.0 ns1 ns2

verifyNorm (NormLInf ns1) (NormL (AtMost a2) ns2) =
        verifyNorms a2 ns1 ns2

verifyNorm (NormL Any ns1) (NormL (AtMost a2) ns2) =
        verifyNorms a2 ns1 ns2

verifyNorm (NormL Any ns1) (NormLInf ns2) =
        verifyNorms 10000.0 ns1 ns2

verifyNorm (NormLInf ns1) (NormL Any ns2) =
        verifyNorms 10000.0 ns1 ns2

verifyNorm (NormL (AtMost a1) ns1) (NormL (AtMost a2) ns2) =
    if (a1 >= a2) then
        verifyNorms a2 ns1 ns2
    else False

-- if our analyzer only computes some lp norm for p /= \infty, then it is definitely not suitable for "Any" norm
verifyNorm (NormL (AtMost _) _) (NormL Any _) =
    False

-- scaling
verifyNorm (NormScale a1 n1) n2 =
    if (a1 <= 1) then
        verifyNorm n1 n2
    else False

verifyNorm n1 (NormScale a2 n2) =
    if (a2 >= 1) then
        verifyNorm n1 n2
    else False

-- this is a base case
verifyNorm NormZero _ = True

verifyNorm _ _ = False

-- here is the main step proving |x_1,...,x_n|_p <= |y_1,...,y_m|_p
-- it tries to prove \forall x_i \exists y_i: x_i <= y_i, such that all y_i are distinct
verifyNorms :: (Show a, Eq a) => Double -> [Norm a] -> [Norm a] -> Bool
verifyNorms p [] nsU = True
verifyNorms p nsE [] = False
verifyNorms p nsE nsU =
  if (length nsE > length nsU) then False
  else

    -- for each nsE element, find all elements in nsU that are not smaller than it
    -- get a binary matrix of results
    let ns = [ (x,[y | y <- nsU]) | x <- nsE] in
    let bss1 = Data.List.map (\(x,ys) -> Data.List.map (verifyNorm x) ys) ns in

    -- check if it is possible to assign a unique y_i to each x_i by counting non-zero columns
    let bss2 = (Data.List.transpose bss1) in
    let bs2  = Data.List.filter exTrue bss2 in
    let b = (length bs2) >= (length nsE) in

    --trace (show(nsU) ++ "\n" ++ show(nsE) ++ "\n" ++ show(p) ++ "\n" ++ show(b)) (if b == True then True
    if b == True then True
    else
        -- if the proof failed, we may try to rearrange the terms
        -- collect the norms for which we did not get a matching
        let nsU' = Data.List.map (\(x,y) -> y) (Data.List.filter (\(x,y) -> not (exTrue x)) (zipWith (\x y -> (x,y)) bss2 nsU)) in
        let nsE' = Data.List.map (\(x,y) -> y) (Data.List.filter (\(x,y) -> not (exTrue x)) (zipWith (\x y -> (x,y)) bss1 nsE)) in

        -- try to group the variables if possible
        let nsU'' = groupLNorm p nsU' in

        -- check if we now have strictly less eleemnts, so that this would not create infinite loops
        if (length nsE == length nsE') && (length nsU == length nsU'') then False else 
        let b2 = verifyNorms p nsE' nsU'' in b2
        --trace (show(nsU) ++ "\n" ++ show(nsU'') ++ "\n" ++ show(nsE) ++ "\n" ++ show(nsE') ++ "\n"  ++ show(p) ++ "\n" ++ show(b2) ++ "\n") b2)
