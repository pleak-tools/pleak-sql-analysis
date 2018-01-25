module Norms where

import Data.Graph.MaxBipartiteMatching
import Data.List
import Data.Map
import Data.Maybe
import Data.Tuple
import qualified Data.Set as S
import Debug.Trace

-- import Expr directly from Banach.hs, 'qualified' because we want to reuse the names
import qualified Banach as B

-- this is a double with additional top-value "any", meaning that any double is allowed at this place
data ADouble = Exactly Double | Any
  deriving Show

-- the composite norm w.r.t. which we compute our sensitivities
-- in the norms, we can use expressions as well as variables
data Norm a = Col a                     -- a variable, if it is toplevel, is treated as its norm (which can be arbitrary)
          | LN (Norm a)
          | NormL     ADouble [Norm a]  -- lp-norm
          | NormLInf  [Norm a]          -- linf-norm
          | NormScale Double (Norm a)   -- scaled norm a * N
          | NormZero (Norm a)           -- the same as NormScale with a -> infinity
  deriving Show

-- we use this value as a flag for subterm grouping function
-- TODO we are actually using only Ungoup, probably we will not need it at all
data Grouping = Group | Ungroup

---------------------------------------------------------------------------------------------
-- TODO: norm derivation for 'expr' and 'tableExpr' is being synchronized with B.Expr and B.TableExpr
deriveNorm :: [a] -> B.Expr -> Norm a
deriveNorm colnames expr = 
    case expr of
        B.PowerLN x _      -> NormL (Exactly 1.0) [LN (Col (colnames !! x))]
        B.Power x _        -> NormL (Exactly 1.0) [Col (colnames !! x)]
        B.ComposePower e c -> deriveNorm colnames e
        B.Exp _ x          -> NormL (Exactly 1.0) [Col (colnames !! x)]
        B.Sigmoid _ _ x    -> NormL (Exactly 1.0) [Col (colnames !! x)]
        B.ScaleNorm a e    -> NormScale a (deriveNorm colnames e)
        B.ZeroSens e       -> NormZero (deriveNorm colnames e)
        B.L p xs           -> NormL (Exactly p) (Data.List.map (\x -> Col (colnames !! x)) xs)
        B.ComposeL p es    -> NormL (Exactly p) (Data.List.map (deriveNorm colnames) es)
        B.LInf xs          -> NormLInf (Data.List.map (\x -> Col (colnames !! x)) xs)
        B.Prod es          -> NormL (Exactly 1.0) (Data.List.map (deriveNorm colnames) es)
        B.Prod2 es         -> deriveNorm colnames (head es) -- we assume that equality of subnorms has been already checked
        B.Min es           -> NormL Any (Data.List.map (deriveNorm colnames) es)
        B.Max es           -> NormL Any (Data.List.map (deriveNorm colnames) es)

deriveTableNorm ::  [a] -> B.TableExpr -> Norm a
deriveTableNorm colnames expr = 
    case expr of

        B.SelectProd es     -> NormL (Exactly 1.0) [deriveNorm colnames (nzHead es)]
        B.SelectMin  es     -> NormL Any [deriveNorm colnames (nzHead es)]
        B.SelectMax  es     -> NormL Any [deriveNorm colnames (nzHead es)]
        B.SelectL p  es     -> NormL (Exactly p) [deriveNorm colnames (nzHead es)]

    -- for simplicity, we assume that the norm is the same for each row
    -- the only difference may come from the toplevel ZeroSens coming from insensitive rows
    where nzHead es = case (head es) of {B.ZeroSens x -> x; x -> x}

-- Let p >= q. We have:
-- ||x|_q, |y|_q, z|_p <= ||x,y|_q, z|_p
-- ||x|_p, |y|_p, z|_q <= ||x,y|_p, z|_q

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
rearrangeNormRec grouping ord Any xs@((NormLInf z):_) =
        let (ys1,ys2) = Data.List.partition (\x -> (case x of {NormLInf _ -> True; Col y -> True;  _ -> False})) xs in
        let ys1' = concat (Data.List.map (\x -> (case x of {NormLInf xs -> xs;  Col y -> [Col y]; _ -> error ("This should not happen, something is wrong")})) ys1) in
        let (ys,zs) = rearrangeNormRec grouping ord Any ys2 in
        case grouping of Group -> if (length ys1' == 0) then (ys,zs) else ((NormLInf ys1'):ys,zs)
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
    case grouping of Group -> if (length ys == 0) then zs else (NormLInf ys):zs
                     Ungroup -> ys ++ zs

rearrangeNorm grouping ord (Exactly p) xs =
    let (ys,zs) = rearrangeNormRec grouping ord (Exactly p) xs in
    case grouping of Group -> if (length ys == 0) then zs else (NormL (Exactly p) ys):zs
                     Ungroup -> ys ++ zs

-- we do some simplifications to make the matching easier
normalizeNorm :: Norm a -> Norm a
-- |||x| ||_p = |x|
normalizeNorm (NormL (Exactly _) [x]) = normalizeNorm x
normalizeNorm (NormLInf [x]) = normalizeNorm x
-- move all scaling into the brackets as deep as possible
normalizeNorm (NormScale 1.0 x) = normalizeNorm x
normalizeNorm (NormScale c1 (NormScale c2 x)) = NormScale (c1*c2) (normalizeNorm x)
normalizeNorm (NormScale c (NormL a xs))  = NormL a  (Data.List.map (\x -> normalizeNorm $ NormScale c x) xs)
normalizeNorm (NormScale c (NormLInf xs)) = NormLInf (Data.List.map (\x -> normalizeNorm $ NormScale c x) xs)
normalizeNorm x = x

-- The number of recursive calls is bounded just for practical safety, there should actually be no loops.
-- The counter is the first parameter, and we increase it only in the function verifyNorms,
--       since only that function may create several branches.
-- The second argument is the expression norm, the third is the database norm.
verifyNorm :: (Show a, Eq a) => Int -> Norm a -> Norm a -> Maybe (Norm a)

-- if there is no certain constructor decomposition, let us just compare the two terms
verifyNorm _ (Col x) (Col y) =
    if x == y then Just (Col x) else Nothing

-- we have x >= ln(x)
verifyNorm k (LN x) y = 
    verifyNorm k (normalizeNorm x) (normalizeNorm y)

-- compare lp-norms
-- if the norm is "Any", we treat it similarly to LInf

-- First, compare the entire first norm with all args of the second norm
-- (we do not do it the other way around since it would not give additional solutions anyway).
-- If it fails, then go deeper into both norms (if possible).
verifyNorm k n1@(Col x) (NormLInf ns2) =
        fmap head (verifyNorms k Any Any [n1] ns2)

verifyNorm k n1@(Col x) (NormL a2 ns2) =
        fmap head (verifyNorms k a2 a2 [n1] ns2)

verifyNorm k n1@(NormLInf ns1) (NormLInf ns2) =
        let ys1 = verifyNorms k Any Any [n1] ns2 in
        let ys = case ys1 of
                     Just _  -> ys1
                     Nothing -> verifyNorms k Any Any ns1 ns2
        in fmap (\zs -> NormLInf zs) ys

verifyNorm k n1@(NormL Any ns1) (NormL Any ns2) =
        let ys1 = verifyNorms k Any Any [n1] ns2 in
        let ys = case ys1 of
                     Just _  -> ys1
                     Nothing -> verifyNorms k Any Any ns1 ns2
        in fmap (\zs -> NormL Any zs) ys

verifyNorm k n1@(NormL Any ns1) (NormLInf ns2) =
        let ys1 = verifyNorms k Any Any [n1] ns2 in
        let ys = case ys1 of
                     Just _  -> ys1
                     Nothing -> verifyNorms k Any Any ns1 ns2
        in fmap (\zs -> NormL Any zs) ys

verifyNorm k n1@(NormLInf ns1) (NormL a2 ns2) =
        let ys1 = verifyNorms k a2 a2 [n1] ns2 in
        let ys = case ys1 of
                     Just _  -> ys1
                     Nothing -> verifyNorms k Any a2 ns1 ns2
        in fmap (\zs -> NormLInf zs) ys

verifyNorm k n1@(NormL Any ns1) (NormL a2 ns2) =
        let ys1 = verifyNorms k a2 a2 [n1] ns2 in
        let ys = case ys1 of
                     Just _  -> ys1
                     Nothing -> verifyNorms k Any a2 ns1 ns2
        in fmap (\zs -> NormL Any zs) ys

verifyNorm k n1@(NormL a1@(Exactly p1) ns1) (NormL a2@(Exactly p2) ns2) =
        let ys1 = verifyNorms k a2 a2 [n1] ns2 in
        let ys = case ys1 of
                     Just _  -> ys1
                     Nothing ->
                        let ys2 = verifyNorms k a1 a2 ns1 ns2 in
                            if (p1 >= p2) then ys2
                            -- TODO check out the exact scaling here!
                            else fmap (\zs -> Data.List.map (\z -> NormScale (p2/p1) z) zs) ys2
        in fmap (\zs -> NormL (Exactly p1) zs) ys

-- if our analyzer only computes some lp norm for p /= \infty, then it is definitely not suitable for "Any" norm
-- however, it may still work if we compare the entire n1 with each arg of n2
-- TODO check if scaling is possible for l_inf
verifyNorm k n1@(NormL (Exactly p) _) (NormL Any ns2) =
        fmap (\x -> NormL (Exactly p) x) (verifyNorms k Any Any [n1] ns2)

-- scaling
verifyNorm k (NormScale a1 n1) (NormScale a2 n2) =
    let y = verifyNorm k n1 n2 in
    fmap (\x -> NormScale a2 x) y

verifyNorm k (NormScale a1 n1) n2 =
    let y = verifyNorm k n1 n2 in
    fmap (\x -> NormScale 1.0 x) y

verifyNorm k n1 (NormScale a2 n2) =
    let y = verifyNorm k n1 n2 in
    fmap (\x -> NormScale a2 x) y

-- this is a base case.
-- actually, NormZero is the largest possible norm.
-- however, we have agreed that NormZero in query norm may contain only insensitive variables.
-- hence, the value under NormZero will always be zero in the cases that are interesting to us
verifyNorm _ (NormZero x) _ = Just (NormZero x)
verifyNorm _ _ _ = Nothing


normalizeAndVerify :: (Show a, Eq a) => Norm a -> Norm a -> Maybe (Norm a)
normalizeAndVerify n1 n2 = 
    verifyNorm 0 (normalizeNorm n1) (normalizeNorm n2)

-- here is the main step proving |x_1,...,x_n|_{px} <= |y_1,...,y_m|_{py} for (py <= px)
-- it tries to prove that there is an injective mapping f such that |x_i| <= |y_f(i)| for all i
verifyNorms :: (Show a, Eq a) => Int -> ADouble ->  ADouble -> [Norm a] -> [Norm a] -> Maybe [Norm a]
verifyNorms _ aX aY [] nsY = Just nsY
verifyNorms _ aX aY nsX [] = Nothing
verifyNorms 10 _ _ _ _     = -- the limit is reached
    trace ("WARNING: reached the limit on recursion depth.") Nothing

verifyNorms k aX aY nsX0 nsY0 =

  -- discard all NormZero entries since we do not need to match them
  let nsX00 = Data.List.filter (\x -> case x of {NormZero _ -> False; _ -> True}) nsX0 in
  let nsY00 = Data.List.filter (\x -> case x of {NormZero _ -> False; _ -> True}) nsY0 in

  -- after discarding NormZero, check the base cases again
  if (length nsX00 == 0) then Just nsY0 else
  if (length nsY00 == 0) then Nothing else

  -- normalize the norms and remove unnecessary constructors to simplify the matching
  let nsX = Data.List.map (\x -> normalizeNorm x) nsX00 in
  let nsY = Data.List.map (\x -> normalizeNorm x) nsY00 in

    -- we label the vertices with integers to define an ordering
    let mapX = (zip [0..length nsX] nsX) in
    let mapY = (zip [0..length nsY] nsY) in

    -- for each nsX element, find all elements in nsY that are not smaller than it (call verifyNorm recursively)
    let ns = [ (x,[y | y <- mapY]) | x <- mapX] in
    let edgeLists = Data.List.map (\((kx,x),ys) -> 
                        Data.List.map (\(ky,newx) -> ((kx,ky),newx))
                            (Data.List.filter (\(_,newx) -> case newx of {Nothing -> False; _ -> True}) 
                                (Data.List.map (\(ky,y) -> (ky,verifyNorm (k+1) x y)) ys)
                            )
                    ) ns
    in

    let alls = concat edgeLists in
    let edgeMap = fromList alls in -- this maps edges to the new x that will be used if this edge is taken
    let (edgeList,_) = Data.List.unzip alls in
    let edges = S.fromList (edgeList) in

    -- get a bipartite graph of results (edges are the '<=' relations), find a maximal matching in it
    let mmapY = matching edges in
    let mmapX = fromList $ Data.List.map swap (toList mmapY) in -- the inverse map, which always exists for a matching

    --trace ("\nnsY: " ++ show mapY ++ "\n" ++
    --       "nsX: " ++ show mapX ++ "\n" ++
    --       "Matching: " ++ show mmapX) $

    -- if we could match all elements of nsX, then we are done
    let b = (length mmapX) >= (length nsX) in
    let maybeMatchedSubnorms = Data.List.map (\edge -> edgeMap ! edge) (toList mmapX) in
    -- bys construction, we have not put Nothing inside, all values should be Just
    let matchedSubnorms = Data.List.map (\x -> case x of Just y -> y) maybeMatchedSubnorms in
    -- the following operation may make the matching easier
    -- however, they may also break the previous matching, so use the next only if the previous has failed
    if (b == True) then Just matchedSubnorms else

        -- if the proof failed, we may try to rearrange the terms
        -- collect only the vertices for which we did not get a matching
        let nsY' = Data.List.map snd (Data.List.filter (\(y,_) -> notMember y mmapY) mapY) in
        let nsX' = Data.List.map snd (Data.List.filter (\(x,_) -> notMember x mmapX) mapX) in

        -- try to ungroup the variables: nsX by aX, nsY by aY, still having "="
        let nsY1 = rearrangeNorm Ungroup LT aY nsY' in
        let nsX1 = rearrangeNorm Ungroup GT aX nsX' in

        let newx1 = if (length nsY1 == length nsY') && (length nsX1 == length nsX') then Nothing else verifyNorms (k+1) aX aY nsX1 nsY1 in
        let b1 = case newx1 of {Nothing -> False; _ -> True} in
        --trace ("b1: nsY: " ++ show(nsY) ++ " --> " ++ show(nsY1) ++ "\n    nsX: " ++ show(nsX) ++ " --> " ++ show(nsX1)) $
        if b1 == True then fmap (matchedSubnorms ++) newx1 else

            -- try to ungroup the variables: nsX,nsY by aX, getting ">=" for nsY
            let nsY2 = rearrangeNorm Ungroup LT aX nsY' in
            let nsX2 = rearrangeNorm Ungroup GT aX nsX' in

            let newx2 = if (length nsY2 == length nsY') && (length nsX2 == length nsX') then Nothing else verifyNorms (k+1) aX aX nsX2 nsY2 in
            let b2 = case newx2 of {Nothing -> False; _ -> True} in
            --trace ("b2: nsY: " ++ show(nsY) ++ " --> " ++ show(nsY2) ++ "\n    nsX: " ++ show(nsX) ++ " --> " ++ show(nsX2)) $
            if b2 == True then fmap (matchedSubnorms ++) newx2 else

                -- try to ungroup the variables: nsX,nsY by aY, getting "<=" for nsX
                let nsY3 = rearrangeNorm Ungroup LT aY nsY' in
                let nsX3 = rearrangeNorm Ungroup GT aY nsX' in

                let newx3 = if (length nsY3 == length nsY') && (length nsX3 == length nsX') then Nothing else verifyNorms (k+1) aY aY nsX3 nsY3 in

                let b3 = case newx3 of {Nothing -> False; _ -> True} in
                --trace ("b3: nsY: " ++ show(nsY) ++ " --> " ++ show(nsY3) ++ "\n    nsX: " ++ show(nsX) ++ " --> " ++ show(nsX3)) $
                fmap (matchedSubnorms ++) newx3




