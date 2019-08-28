module AexprQ where

import Data.List
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace
import ErrorMsg
import ExprQ
import GroupQ
import VarstateQ
import RangeUtils

-- the default alpha value for Tauoids and Sigmoids
a = 0.1

-- we want to parse complex expressions and transform them to Expr afterwards
data AExpr a
  = AVar a
  | AConst Double
  | AText String
  | ASubExpr String a Bool
  | AUnary  AUnOp (AExpr a)
  | ABinary ABinOp (AExpr a) (AExpr a)
  | AZeroSens (AExpr a) -- in some cases, we need to deliberately force ZeroSens (also around sensitive expressions), be careful with this construction!
  | AAbs  (AExpr a)
  | ASum  [AExpr a]
  | AProd [AExpr a]
  | AMins [AExpr a]
  | AMaxs [AExpr a]
  | AAnds [AExpr a]
  | AOrs  [AExpr a]
  | AXors [AExpr a] -- we assume that it is applied only to mutually exclusive conditions
  | AVector [AExpr a]
  deriving (Show)

data AUnOp
  = AAbsBegin | AAbsEnd 
  | ALn
  | AFloor
  | ANeg | ANot
  | AExp   Double
  | APower Double
  deriving (Show)

data ABinOp
  = ADiv | AMult | AAdd | ASub
  | AMin | AMax 
  | AAnd | AOr | AXor
  | ALTint | ALEint | AEQint | AGTint | AGEint
  | ALT | ALE | AEQ | AGE | AGT | ALike
  | AEQstr
  | ADistance
  deriving (Show)

data AType = AInt | AFloat | ABool | AString | AUnit deriving (Eq, Show)

instance Ord AType where
    compare ABool AInt = LT
    compare AInt AFloat = LT
    compare ABool AFloat = LT
    compare _ AString = LT
    compare AUnit _ = LT
    compare AInt ABool = GT
    compare AFloat AInt = GT
    compare AFloat ABool = GT
    compare AString _ = GT
    compare _ AUnit = GT
    compare x y = if x == y then EQ else error $ error_badTypes x y

stringToAType :: String -> AType
stringToAType "int"   = AInt
stringToAType "float" = AFloat
stringToAType "bool"  = ABool
stringToAType "text"  = AString
stringToAType t     = error $ error_typeDoesNotExist t

-- this has been stolen from Data.Logic.Propositional.NormalForms and adjusted to our data types
neg :: AExpr a -> AExpr a
neg = AUnary ANot

disj :: AExpr a -> AExpr a -> AExpr a
disj = ABinary AOr

conj :: AExpr a -> AExpr a -> AExpr a
conj = ABinary AAnd

toNNF :: AExpr a -> AExpr a
toNNF (AUnary ANot (AUnary ANot expr))       = toNNF expr

toNNF (ABinary AAnd exp1 exp2)              = toNNF exp1 `conj` toNNF exp2
toNNF (AUnary ANot (ABinary AAnd exp1 exp2)) = toNNF $ neg exp1 `disj` neg exp2

toNNF (ABinary AOr exp1 exp2)               = toNNF exp1 `disj` toNNF exp2
toNNF (AUnary ANot (ABinary AOr exp1 exp2))  = toNNF $ neg exp1 `conj` neg exp2

toNNF expr                                 = expr

toCNF :: AExpr a -> AExpr a
toCNF = toCNF' . toNNF
  where
    toCNF' :: AExpr a -> AExpr a
    toCNF' (ABinary AAnd exp1 exp2) = toCNF' exp1 `conj` toCNF' exp2
    toCNF' (ABinary AOr  exp1 exp2) = toCNF' exp1 `dist` toCNF' exp2
    toCNF' expr                    = expr
    
    dist :: AExpr a -> AExpr a -> AExpr a
    dist (ABinary AAnd e11 e12) e2 = (e11 `dist` e2) `conj` (e12 `dist` e2)
    dist e1 (ABinary AAnd e21 e22) = (e1 `dist` e21) `conj` (e1 `dist` e22)
    dist e1 e2                    = e1 `disj` e2

toDNF :: AExpr a -> AExpr a
toDNF = toDNF' . toNNF
  where
    toDNF' :: AExpr a -> AExpr a
    toDNF' (ABinary AAnd exp1 exp2) = toDNF' exp1 `dist` toDNF' exp2
    toDNF' (ABinary AOr exp1 exp2) = toDNF' exp1 `disj` toDNF' exp2
    toDNF' expr                    = expr

    dist :: AExpr a -> AExpr a -> AExpr a
    dist (ABinary AOr e11 e12) e2 = (e11 `dist` e2) `disj` (e12 `dist` e2)
    dist e1 (ABinary AOr e21 e22) = (e1 `dist` e21) `disj` (e1 `dist` e22)
    dist e1 e2                    = e1 `conj` e2

-- This does not take into account negations
fromDNFtoList :: (Show a) => AExpr a -> [[a]]
fromDNFtoList expr =
    case expr of
        (ABinary AOr  exp1 exp2) -> fromDNFtoList exp1 ++ fromDNFtoList exp2
        (ABinary AAnd exp1 exp2) -> zipWith (++) (fromDNFtoList exp1) (fromDNFtoList exp2)
        (AUnary ANot  exp)       -> fromDNFtoList exp
        (AVar x)                 -> [[x]]

-- fix the abs constructions
aexprFixAbs (AUnary AAbsEnd (AUnary AAbsBegin x)) = AAbs (aexprFixAbs x)

-- if none of the previous cases matched, go deeper into the term
aexprFixAbs (AUnary f x)    = AUnary  f (aexprFixAbs x)
aexprFixAbs (ABinary f x y) = ABinary f (aexprFixAbs x) (aexprFixAbs y)
aexprFixAbs x = x

-- some normalization to simplify the transformation, merge some binary operations to n-ary
aexprNormalize :: AExpr a -> AExpr a
aexprNormalize (ABinary AAdd x y) =
            let f  = id in
            let x' = aexprNormalize x in
            let y' = aexprNormalize y in
            case (x',y') of
                (ASum xs, ASum ys) -> ASum (xs ++ map f ys)
                (ASum xs, _      ) -> ASum (f y':xs)
                (_      , ASum ys) -> ASum (x': map f ys)
                (_      , _      ) -> ASum [x',f y']

aexprNormalize (ABinary ASub x y) =
            let f  = AUnary ANeg in
            let x' = aexprNormalize x in
            let y' = aexprNormalize y in
            case (x',y') of
                (ASum xs, ASum ys) -> ASum (xs ++ map f ys)
                (ASum xs, _      ) -> ASum (f y':xs)
                (_      , ASum ys) -> ASum (x': map f ys)
                (_      , _      ) -> ASum [x',f y']

aexprNormalize (ABinary AMult x y) =
            let f  = id in
            let x' = aexprNormalize x in
            let y' = aexprNormalize y in
            case (x',y') of
                (AProd xs, AProd ys) -> AProd (xs ++ map f ys)
                (AProd xs, _       ) -> AProd (f y':xs)
                (_       , AProd ys) -> AProd (x': map f ys)
                (_       , _       ) -> AProd [x',f y']

aexprNormalize (ABinary ADiv x y) =
            let f = (\v -> AUnary (APower (-1.0)) v) in
            let x' = aexprNormalize x in
            let y' = aexprNormalize y in
            case (x',y') of
                (AProd xs, AProd ys) -> AProd (xs ++ map f ys)
                (AProd xs, _       ) -> AProd (f y':xs)
                (_       , AProd ys) -> AProd (x': map f ys)
                (_       , _       ) -> AProd [x',f y']

aexprNormalize (ABinary AMin x y) =
            let f  = id in
            let x' = aexprNormalize x in
            let y' = aexprNormalize y in
            case (x',y') of
                (AMins xs, AMins ys) -> AMins (xs ++ map f ys)
                (AMins xs, _       ) -> AMins (f y':xs)
                (_       , AMins ys) -> AMins (x': map f ys)
                (_       , _       ) -> AMins [x',f y']

aexprNormalize (ABinary AMax x y) =
            let f  = id in
            let x' = aexprNormalize x in
            let y' = aexprNormalize y in
            case (x',y') of
                (AMaxs xs, AMaxs ys) -> AMaxs (xs ++ map f ys)
                (AMaxs xs, _       ) -> AMaxs (f y':xs)
                (_       , AMaxs ys) -> AMaxs (x': map f ys)
                (_       , _       ) -> AMaxs [x',f y']

aexprNormalize (ABinary AAnd x y) =
            let f  = id in
            let x' = aexprNormalize x in
            let y' = aexprNormalize y in
            case (x',y') of
                (AAnds xs, AAnds ys) -> AAnds (xs ++ map f ys)
                (AAnds xs, _       ) -> AAnds (f y':xs)
                (_       , AAnds ys) -> AAnds (x': map f ys)
                (_       , _       ) -> AAnds [x',f y']

aexprNormalize (ABinary AOr x y) =
            let f  = id in
            let x' = aexprNormalize x in
            let y' = aexprNormalize y in
            case (x',y') of
                (AOrs xs, AOrs ys) -> AOrs (xs ++ map f ys)
                (AOrs xs, _      ) -> AOrs (f y':xs)
                (_      , AOrs ys) -> AOrs (x': map f ys)
                (_      , _      ) -> AOrs [x',f y']

aexprNormalize (ABinary AXor x y) =
            let f  = id in
            let x' = aexprNormalize x in
            let y' = aexprNormalize y in
            case (x',y') of
                (AXors xs, AXors ys) -> AXors (xs ++ map f ys)
                (AXors xs, _       ) -> AXors (f y':xs)
                (_       , AXors ys) -> AXors (x': map f ys)
                (_       , _       ) -> AXors [x',f y']

--aexprNormalize (ABinary AAnd x y) = aexprNormalize $ ABinary AMult x y
--aexprNormalize (ABinary AOr  x y) = aexprNormalize $ ABinary ASub (ABinary AAdd x y) (ABinary AMult x y)

aexprNormalize (AUnary AAbsEnd (AUnary AAbsBegin x)) = AAbs (aexprNormalize x)

-- if none of the previous cases matched, go deeper into the term
aexprNormalize (AUnary f x)    = AUnary  f (aexprNormalize x)
aexprNormalize (ABinary f x y) = ABinary f (aexprNormalize x) (aexprNormalize y)

aexprNormalize (AZeroSens x) = AZeroSens $ aexprNormalize x
aexprNormalize (AAbs x) = AAbs $ aexprNormalize x
aexprNormalize (ASum  xs) = ASum  $ map aexprNormalize xs
aexprNormalize (AProd xs) = AProd $ map aexprNormalize xs
aexprNormalize (AMins xs) = AMins $ map aexprNormalize xs
aexprNormalize (AMaxs xs) = AMaxs $ map aexprNormalize xs
aexprNormalize (AAnds xs) = AAnds $ map aexprNormalize xs
aexprNormalize (AOrs  xs) = AOrs  $ map aexprNormalize xs
aexprNormalize (AXors xs) = AXors $ map aexprNormalize xs
aexprNormalize (AVector xs) = AVector $ map aexprNormalize xs

aexprNormalize x = x

---------------------------------------------------------------------------------------------------------
-- we do not convert to aggregation since it comes separately
-- we do not convert to scaleNorm and zeroSens since they come from the database norm
aexprToExpr :: VarName -> AExpr VarName -> (M.Map VarName Expr)

-- TODO this is temporary, can be improved
--aexprToExpr y (AVar "min~") = M.fromList [(y,ARMin)]
--aexprToExpr y (AVar "max~") = M.fromList [(y,ARMax)]

--
aexprToExpr y (AUnary AFloor x) = aexprToExpr y x

aexprToExpr y (AText s) = M.fromList [(y, Text s)]

aexprToExpr y (AUnary (AExp c) (AVar x)) = M.fromList [(y, Exp c x)]
aexprToExpr y (AUnary (AExp c) x) = 
    let z = y ++ "~0" in
    M.union (aexprToExpr z x) $ M.fromList [(y, Exp c z)]

aexprToExpr y (AUnary ANeg (AConst c)) = M.fromList [(y, Const (-c))]
aexprToExpr y (AUnary ANeg x) =
    let z      = y ++ "~0" in
    M.union (aexprToExpr z x) $ M.fromList [(y, Prod ["-1", z]), ("-1", Const (-1.0))]

aexprToExpr y (AUnary ANot x) = 
    let z      = y ++ "~0" in
    let w      = y ++ "~1" in
    M.union (aexprToExpr z x) $ M.fromList [(y, Sum["1",w]), (w, Prod ["-1", z]), ("1", Const (1.0)), ("-1", Const (-1.0))]

aexprToExpr y (AConst c)   = M.fromList [(y, Const c)]
aexprToExpr y (AVar x)     = M.fromList [(y, Id x)]
-- TODO see what we actually want here
aexprToExpr y (ASubExpr t x _) = M.fromList [(y, Id (t ++ [tsep] ++ x))]

aexprToExpr y (ABinary ALike x1 x2) =
    let z1     = y ++ "~1" in
    let z2     = y ++ "~2" in
    M.union (aexprToExpr z1 x1) $ M.union (aexprToExpr z2 x2) $ M.fromList [(y, Like z1 z2)]

aexprToExpr y (ABinary ALEint x2 x1) = 
    aexprToExpr y (ABinary AGEint x1 x2)

aexprToExpr y (ABinary ALTint x2 x1) = 
    aexprToExpr y (ABinary AGTint x1 x2)

aexprToExpr y (ABinary ALE x2 x1) = 
    aexprToExpr y (ABinary AGE x1 x2)

aexprToExpr y (ABinary ALT x2 x1) = 
    aexprToExpr y (ABinary AGT x1 x2)

--aexprToExpr y (ABinary ALT x (AConst c)) = 
--    let z      = y ++ "~0" in
--    let w1     = y ++ "~1" in
--    let w2     = y ++ "~2" in
--    M.union (aexprToExpr z x) $ M.fromList [(y, Sum ["1",w2]), (w2, Prod ["-1",w1]), (w1, Sigmoid a c z), ("1", Const (1.0)), ("-1", Const (-1.0))]

aexprToExpr y (ABinary AEQstr x1 x2) = 
    let z      = y ++ "~0" in 
    let z1     = y ++ "~1" in
    let z2     = y ++ "~2" in
    M.union (aexprToExpr z1 x1) $ M.union (aexprToExpr z2 x2) $ M.fromList [(y, CompStr z1 z2)]

aexprToExpr y (ABinary AEQint x2 x1) = 
    let z      = y ++ "~0" in 
    let z1     = y ++ "~1" in
    let z2     = y ++ "~2" in
    M.union (aexprToExpr z1 x1) $ M.union (aexprToExpr z2 x2) $ M.fromList [(y, CompInt EQ z1 z2)]

aexprToExpr y (ABinary AEQ x1 x2) = 
    let z      = y ++ "~0" in 
    let z1     = y ++ "~1" in
    let z2     = y ++ "~2" in
    M.union (aexprToExpr z1 x1) $ M.union (aexprToExpr z2 x2) $ M.fromList [(y, Comp EQ z1 z2)]

--aexprToExpr y (ABinary AEQ x (AConst c)) = 
--    let z      = y ++ "~0" in
--    M.union (aexprToExpr z x) $ M.fromList [(y, Tauoid  a c z)]

aexprToExpr y (ABinary AGEint x1 x2) = 
    let z      = y ++ "~0" in 
    let z1     = y ++ "~1" in
    let z2     = y ++ "~2" in
    let w1     = y ++ "~3" in
    let w2     = y ++ "~4" in
    M.union (aexprToExpr z1 x1) $ M.union (aexprToExpr z2 x2) $ M.fromList [(y, Max [w1, w2]), (w1, CompInt GT z1 z2), (w2, CompInt EQ z1 z2)]

aexprToExpr y (ABinary AGTint x1 x2) = 
    let z      = y ++ "~0" in 
    let z1     = y ++ "~1" in
    let z2     = y ++ "~2" in
    M.union (aexprToExpr z1 x1) $ M.union (aexprToExpr z2 x2) $ M.fromList [(y, CompInt GT z1 z2)]

aexprToExpr y (ABinary AGE x1 x2) = aexprToExpr y (ABinary AGT x1 x2)

aexprToExpr y (ABinary AGT x1 x2) = 
    let z      = y ++ "~0" in
    let z1     = y ++ "~1" in
    let z2     = y ++ "~2" in
    M.union (aexprToExpr z1 x1) $ M.union (aexprToExpr z2 x2) $ M.fromList [(y, Comp GT z1 z2)]

--aexprToExpr y (ABinary AGT x (AConst c)) = 
--    let z      = y ++ "~0" in
--    let z1     = y ++ "~1" in
--    M.union (aexprToExpr z x) $ M.fromList [(y, Sigmoid a c z)]

-- l2-norm
aexprToExpr y aexpr@(ABinary ADistance (AVector xs1) (AVector xs2)) =
    if length xs1 /= length xs2 then error $ error_queryExpr_pointDistanceLen aexpr else
    let n = length xs1 in
    let zs  = map (\x -> y ++ "~0~" ++ show x) [0..n-1] in
    let zs1 = map (\x -> y ++ "~1~" ++ show x) [0..n-1] in
    let zs2 = map (\x -> y ++ "~2~" ++ show x) [0..n-1] in
    let zs3 = map (\x -> y ++ "~3~" ++ show x) [0..n-1] in
    
    let ws1 = zipWith aexprToExpr zs1 xs1 in
    let ws2 = zipWith aexprToExpr zs2 xs2 in

    let ws = M.fromList $ concat $ zipWith4 (\z z1 z2 z3 -> [(z, Sum [z1,z3]), (z3, Prod ["-1", z2]), ("-1", Const (-1.0))]) zs zs1 zs2 zs3 in
    M.union (foldr M.union ws (ws1 ++ ws2)) $ M.fromList [(y, L 2.0 zs)]

-- lp-norm
aexprToExpr y aexpr@(AUnary (APower pinv) (ASum xs)) =

    let p = 1 / pinv in

    -- if p is an even number, we do not need to take absolute value of the arguments
    let pint = round p in
    let isEven = (mod pint 2 == 0) && (p == fromIntegral pint) in

    -- collect all expression and variable arguments separately
    let ysExpr = filter (\x -> case x of {AUnary (APower q) (AAbs _)        -> p == q;
                                          AUnary (APower q) _        -> p == q && isEven;
                                          _ -> False}) xs in
    let ysVar  = filter (\x -> case x of {AUnary (APower q) (AAbs (AVar _)) -> p == q; AUnary (APower q) (AVar _) -> p == q && isEven; _ -> False}) xs in

        -- if all arguments are p-powers of absolute values, then we have an lp-norm
        if (length xs == length ysExpr) then

            -- if there is at least one expression argument that is not a variable, convert all variables to expressions as x~ = Power x 1.0
            if (length ysVar < length ysExpr) then
                let zs = map (\x -> y ++ "~" ++ show x) [0..length xs-1] in
                let ws = map (\(x,z) -> case x of {AUnary (APower _) (AAbs x') -> aexprToExpr z x'; AUnary (APower _) x' -> aexprToExpr z x'}) (zip xs zs) in
                M.union (foldr M.union M.empty ws) $ M.fromList [(y, L p zs)]

            -- otherwise, take the variables directly
            else
                let zs = map (\x -> case x of {AUnary (APower _) (AAbs (AVar z)) -> z; AUnary (APower _) (AVar z) -> z}) xs in
                M.fromList[(y, L p zs)]

        -- otherwise, we fail since we do not know how to compute root sensitivities yet
        else error $ error_queryExpr aexpr

aexprToExpr y aexpr@(AUnary (APower pinv) (AUnary (APower q) (AAbs (AVar x)))) =
    let p = 1 / pinv in
    if p == q then
        M.fromList [(y, L p [x])]
    else error $ error_queryExpr aexpr

aexprToExpr y aexpr@(AUnary (APower pinv) (AUnary (APower q) (AAbs x))) =
    let p = 1 / pinv in
    if p == q then
        let z = y ++ "~0" in
        M.union (aexprToExpr z x) $ M.fromList [(y, L p [z])]
    else error $ error_queryExpr aexpr

aexprToExpr y aexpr@(AUnary (APower pinv) (AUnary (APower q) (AVar x))) =

    -- if p is an even number, we do not need to take absolute value of the arguments
    let p = 1 / pinv in
    let pint = round p in
    let isEven = (mod pint 2 == 0) && (p == fromIntegral pint) in
    if p == q && isEven then
        M.fromList [(y, L p [x])]
    else error $ error_queryExpr aexpr

aexprToExpr y aexpr@(AUnary (APower pinv) (AUnary (APower q) x)) =

    -- if p is an even number, we do not need to take absolute value of the arguments
    let p = 1 / pinv in
    let pint = round p in
    let isEven = (mod pint 2 == 0) && (p == fromIntegral pint) in
    if p == q && isEven then
        let z = y ++ "~0" in
        M.union (aexprToExpr z x) $ M.fromList [(y, L p [z])]
    else error $ error_queryExpr aexpr

aexprToExpr y (AUnary (APower c) (AVar x)) = 
    if c >= 1 then
        M.fromList [(y, Power x c)]
    else
        M.fromList [(y, PowerLN x c)]

aexprToExpr y (AUnary (APower c) (AConst x)) = 
    M.fromList [(y, Const (x**c))]

aexprToExpr y (AUnary (APower c) x) = 
    let z = y ++ "~0" in
    M.union (aexprToExpr z x) $ M.fromList [(y, Power z c)]

-- l1-norm and sum
aexprToExpr y aexpr@(ASum xs) =

    -- collect all expression and variable arguments separately
    let ysExpr = filter (\x -> case x of {AAbs _        -> True; _ -> False}) xs in
    let ysVar  = filter (\x -> case x of {AAbs (AVar _) -> True; _ -> False}) xs in

        -- if all arguments are absolute values, then we have an l1-norm
        if (length xs == length ysExpr) then

            -- if there is at least one expression argument that is not a variable, convert all variables to expressions as z~ = Power z 1.0
            if (length ysVar < length ysExpr) then
                let zs = map (\x -> y ++ "~" ++ show x) [0..length xs-1] in
                let ws = map (\(x,z) -> case x of AAbs x' -> aexprToExpr z x') (zip xs zs) in
                M.union (foldr M.union M.empty ws) $ M.fromList [(y, L 1.0 zs)]

            -- otherwise, take the variables directly
            else
                let zs = map (\x -> case x of {AAbs (AVar z) -> z}) xs in
                M.fromList [(y, L 1.0 zs)]

            -- otherwise, we have a sum
            else
                    let zs = map (\x -> y ++ "~" ++ show x) [0..length xs-1] in
                    let ws = map (\(x,z) -> aexprToExpr z x) (zip xs zs) in
                    M.union (foldr M.union M.empty ws) $ M.fromList [(y, Sum zs)]

aexprToExpr y (AAbs (AVar x)) = M.fromList [(y, L 1.0 [x])]

aexprToExpr y (AAbs x) =
    let z = y ++ "~0" in
    M.union (aexprToExpr z x) $ M.fromList [(y, L 1.0 [z])]

aexprToExpr y (AZeroSens x) = 
    let z = y ++ "~0" in
    M.union (aexprToExpr z x) $ M.fromList [(y, ZeroSens z)]

-- linf-norm
aexprToExpr y (AMaxs xs) =

            -- if all arguments are absolute values, then we have an linf-norm
            let ys = filter (\x -> case x of {AAbs (AVar _) -> True; _ -> False}) xs in
            if length ys == length xs then
                        let zs = map (\x -> case x of AAbs (AVar x') -> x') xs in
                        M.fromList [(y, LInf zs)]

            -- otherwise, we have a max
            else
                let zs = map (\x -> y ++ "~" ++ show x) [0..length xs-1] in
                let ws = map (\(x,z) -> aexprToExpr z x) (zip xs zs) in
                M.union (foldr M.union M.empty ws) $ M.fromList [(y, Max zs)]

aexprToExpr y (AMins xs) =
    let zs = map (\x -> y ++ "~" ++ show x) [0..length xs-1] in
    let ws = map (\(x,z) -> aexprToExpr z x) (zip xs zs) in
    M.union (foldr M.union M.empty ws) $ M.fromList [(y, Min zs)]

aexprToExpr y (AProd xs) =
    let zs = map (\x -> y ++ "~" ++ show x) [0..length xs-1] in
    let ws = map (\(x,z) -> aexprToExpr z x) (zip xs zs) in
    M.union (foldr M.union M.empty ws) $ M.fromList [(y, Prod zs)]

aexprToExpr y (AAnds xs) = aexprToExpr y $ AMins xs
aexprToExpr y (AOrs  xs) = aexprToExpr y $ AMaxs xs --AUnary ANot (AProd (map (AUnary ANot) xs))
aexprToExpr y (AXors xs) = aexprToExpr y $ ASum xs


-- we may possibly add more interesting expressions that can be reduced to Expr
aexprToExpr y aexpr = error $ error_queryExpr aexpr
------------------------------------------------------------------------------------
aexprLpnorm p xs = AUnary (APower (1/p)) $ ASum $ map (AUnary (APower p) . AAbs) xs
aexprLinfnorm xs = AMaxs $ map AAbs xs

aexprToString :: AExpr String -> String
aexprToString aexpr =
    case aexpr of
        AVar x -> x
        AConst c -> show c
        AText s -> s

        ASubExpr t x _ -> t ++ [tsep] ++ x
        AZeroSens x -> aexprToString x

        AAbs x -> "abs(" ++ aexprToString x ++ ")"
        ASum xs -> "(" ++ intercalate " + " (map aexprToString xs) ++ ")"
        AProd xs -> "(" ++ intercalate " * " (map aexprToString xs) ++ ")"
        AMins xs -> "least(" ++ intercalate "," (map aexprToString xs) ++ ")"
        AMaxs xs -> "greatest(" ++ intercalate "," (map aexprToString xs) ++ ")"
        AAnds xs -> "(" ++ intercalate " AND " (map aexprToString xs) ++ ")"
        AOrs  xs -> "(" ++ intercalate " OR " (map aexprToString xs) ++ ")"
        AXors xs -> "(" ++ intercalate " OR " (map aexprToString xs) ++ ")"
        AVector xs -> "point(" ++ intercalate "," (map aexprToString xs) ++ ")"

        AUnary ALn x -> "log(" ++ aexprToString x ++ ")"
        AUnary AFloor x -> "floor(" ++ aexprToString x ++ ")"
        AUnary ANeg x -> "( - " ++ aexprToString x ++ ")"
        AUnary ANot x -> "not(" ++ aexprToString x ++ ")"
        AUnary (AExp c) x -> "exp(" ++ show c ++ " * " ++ aexprToString x ++ ")"
        AUnary (APower c) x -> "(" ++ aexprToString x ++ " ^ " ++ show c ++ ")"

        ABinary ADiv x1 x2 -> "(" ++ aexprToString x1 ++ " / " ++ aexprToString x2 ++ ")"
        ABinary AMult x1 x2 -> "(" ++ aexprToString x1 ++ " * " ++ aexprToString x2 ++ ")"
        ABinary AAdd x1 x2 -> "(" ++ aexprToString x1 ++ " + " ++ aexprToString x2 ++ ")"
        ABinary ASub x1 x2 -> "(" ++ aexprToString x1 ++ " - " ++ aexprToString x2 ++ ")"
        ABinary AMin x1 x2 -> "least(" ++ aexprToString x1 ++ ", " ++ aexprToString x2 ++ ")"
        ABinary AMax x1 x2 -> "greatest(" ++ aexprToString x1 ++ ", " ++ aexprToString x2 ++ ")"
        ABinary AAnd x1 x2 -> "(" ++ aexprToString x1 ++ " AND " ++ aexprToString x2 ++ ")"
        ABinary AOr  x1 x2 -> "(" ++ aexprToString x1 ++ " OR " ++ aexprToString x2 ++ ")"
        ABinary AXor  x1 x2 -> "(" ++ aexprToString x1 ++ " OR " ++ aexprToString x2 ++ ")"
        ABinary ALT x1 x2  -> "(" ++ aexprToString x1 ++ " < " ++ aexprToString x2 ++ ")"
        ABinary ALE x1 x2  -> "(" ++ aexprToString x1 ++ " <= " ++ aexprToString x2 ++ ")"
        ABinary AEQ x1 x2  -> "(" ++ aexprToString x1 ++ " = " ++ aexprToString x2 ++ ")"
        ABinary AGE x1 x2  -> "(" ++ aexprToString x1 ++ " >= " ++ aexprToString x2 ++ ")"
        ABinary AGT x1 x2  -> "(" ++ aexprToString x1 ++ " > " ++ aexprToString x2 ++ ")"
        ABinary ALTint x1 x2 -> "(" ++ aexprToString x1 ++ " < " ++ aexprToString x2 ++ ")"
        ABinary ALEint x1 x2 -> "(" ++ aexprToString x1 ++ " <= " ++ aexprToString x2 ++ ")"
        ABinary AEQint x1 x2 -> "(" ++ aexprToString x1 ++ " = " ++ aexprToString x2 ++ ")"
        ABinary AGEint x1 x2 -> "(" ++ aexprToString x1 ++ " >= " ++ aexprToString x2 ++ ")"
        ABinary AGTint x1 x2 -> "(" ++ aexprToString x1 ++ " > " ++ aexprToString x2 ++ ")"
        ABinary AEQstr x1 x2 -> "(" ++ aexprToString x1 ++ " = " ++ aexprToString x2 ++ ")"
        ABinary ALike x1 x2 -> "(" ++ aexprToString x1 ++ " LIKE " ++ aexprToString x2 ++ ")"
        -- we have this complicated workaroud since <@> is a strange operation that is not supported by default
        ABinary ADistance (AVector xs1) (AVector xs2) -> "(" ++ (intercalate "+" ts) ++ ")^0.5"
            where ts = zipWith (\x1 x2 -> "((" ++ aexprToString x1 ++ ") - (" ++ aexprToString x2 ++ "))^2") xs1 xs2
        ABinary ADistance x1 x2 -> "(" ++ aexprToString x1 ++ " <@> " ++ aexprToString x2 ++ ")"

------------------------------------------------------------------------------------
updatePreficesAexpr :: (S.Set String) -> VarName -> AExpr VarName -> AExpr VarName
updatePreficesAexpr fullTablePaths prefix aexpr =
    case aexpr of
        AVar x -> AVar $ processBase x
        AConst c -> AConst c
        AText c -> AText c

        ASubExpr t x g -> ASubExpr (processBase t) x g
        AZeroSens x -> AZeroSens $ processRec x

        AAbs x -> AAbs $ processRec x
        ASum xs -> ASum (map processRec xs)
        AProd xs -> AProd (map processRec xs)
        AMins xs -> AMins (map processRec xs)
        AMaxs xs -> AMaxs (map processRec xs)
        AAnds xs -> AAnds (map processRec xs)
        AOrs  xs -> AOrs (map processRec xs)
        AXors xs -> AXors (map processRec xs)
        AVector xs -> AVector (map processRec xs)

        AUnary ALn x -> AUnary ALn $ processRec x
        AUnary AFloor x -> AUnary AFloor $ processRec x
        AUnary ANeg x -> AUnary ANeg $ processRec x
        AUnary ANot x -> AUnary ANot $ processRec x
        AUnary (AExp c) x -> AUnary (AExp c) $ processRec x
        AUnary (APower c) x -> AUnary (APower c) $ processRec x

        ABinary ADiv x1 x2 -> ABinary ADiv (processRec x1) (processRec x2)
        ABinary AMult x1 x2 -> ABinary AMult (processRec x1) (processRec x2)
        ABinary AAdd x1 x2 -> ABinary AAdd (processRec x1) (processRec x2)
        ABinary ASub x1 x2 -> ABinary ASub (processRec x1) (processRec x2)
        ABinary AMin x1 x2 -> ABinary AMin (processRec x1) (processRec x2)
        ABinary AMax x1 x2 -> ABinary AMax (processRec x1) (processRec x2)
        ABinary AAnd x1 x2 -> ABinary AAnd (processRec x1) (processRec x2)
        ABinary AOr  x1 x2 -> ABinary AOr (processRec x1) (processRec x2)
        ABinary AXor x1 x2 -> ABinary AXor (processRec x1) (processRec x2)
        ABinary ALT x1 x2  -> ABinary ALT (processRec x1) (processRec x2)
        ABinary ALE x1 x2  -> ABinary ALE (processRec x1) (processRec x2)
        ABinary AEQ  x1 x2 -> ABinary AEQ (processRec x1) (processRec x2)
        ABinary AGT x1 x2  -> ABinary AGT (processRec x1) (processRec x2)
        ABinary AGE x1 x2  -> ABinary AGE (processRec x1) (processRec x2)
        ABinary AEQstr x1 x2 -> ABinary AEQstr (processRec x1) (processRec x2)
        ABinary ALTint x1 x2 -> ABinary ALTint (processRec x1) (processRec x2)
        ABinary ALEint x1 x2 -> ABinary ALEint (processRec x1) (processRec x2)
        ABinary AEQint x1 x2 -> ABinary AEQint (processRec x1) (processRec x2)
        ABinary AGEint x1 x2 -> ABinary AGEint (processRec x1) (processRec x2)
        ABinary AGTint x1 x2 -> ABinary AGTint (processRec x1) (processRec x2)
        ABinary ALike x1 x2 -> ABinary ALike (processRec x1) (processRec x2)
        ABinary ADistance x1 x2 -> ABinary ADistance (processRec x1) (processRec x2)

   where processRec  x = updatePreficesAexpr fullTablePaths prefix x
         processBase x = updatePrefices      fullTablePaths prefix x

--------------------------
-- get all variables
getAllAExprVars :: (Ord a, Show a) => Bool -> AExpr a -> S.Set a
getAllAExprVars sensOnly aexpr =
    case aexpr of
        AVar x -> processBase x
        AConst c -> S.empty
        AText c -> S.empty

        -- TODO check if we want treat subtable outputs as variables
        ASubExpr _ _ _ -> S.empty
        AZeroSens x  -> if sensOnly then S.empty else processRec x

        AAbs x  -> processRec x
        ASum  xs -> foldr S.union S.empty $ map processRec xs
        AProd xs -> foldr S.union S.empty $ map processRec xs
        AMins xs -> foldr S.union S.empty $ map processRec xs
        AMaxs xs -> foldr S.union S.empty $ map processRec xs
        AAnds xs -> foldr S.union S.empty $ map processRec xs
        AOrs  xs -> foldr S.union S.empty $ map processRec xs
        AXors xs -> foldr S.union S.empty $ map processRec xs
        AVector xs -> foldr S.union S.empty $ map processRec xs

        AUnary ALn x -> processRec x
        AUnary AFloor x -> processRec x
        AUnary ANeg x -> processRec x
        AUnary ANot x -> processRec x
        AUnary (AExp c) x -> processRec x
        AUnary (APower c) x -> processRec x

        ABinary ADiv x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AMult x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AAdd x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary ASub x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AMin x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AMax x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AAnd x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AOr  x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AXor x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary ALT x1 x2  -> S.union (processRec x1) (processRec x2)
        ABinary ALE x1 x2  -> S.union (processRec x1) (processRec x2)
        ABinary AEQ  x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AGE x1 x2  -> S.union (processRec x1) (processRec x2)
        ABinary AGT x1 x2  -> S.union (processRec x1) (processRec x2)
        ABinary AEQstr x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary ALTint x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary ALEint x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AEQint x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AGEint x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AGTint x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary ALike x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary ADistance x1 x2 -> S.union (processRec x1) (processRec x2)
    where processRec x = getAllAExprVars sensOnly x
          processBase x = S.singleton x

--------------------------
-- get all variables
getAllSubExprs :: (Ord a, Show a) => Bool -> AExpr a -> S.Set ((String,a),Bool)
getAllSubExprs sensOnly aexpr =
    case aexpr of
        AVar x -> S.empty
        AConst c -> S.empty
        AText c -> S.empty

        ASubExpr t x g -> processBase ((t,x),g)
        AZeroSens x  -> if sensOnly then S.empty else processRec x

        AAbs x  -> processRec x
        ASum  xs -> foldr S.union S.empty $ map processRec xs
        AProd xs -> foldr S.union S.empty $ map processRec xs
        AMins xs -> foldr S.union S.empty $ map processRec xs
        AMaxs xs -> foldr S.union S.empty $ map processRec xs
        AAnds xs -> foldr S.union S.empty $ map processRec xs
        AOrs  xs -> foldr S.union S.empty $ map processRec xs
        AXors xs -> foldr S.union S.empty $ map processRec xs
        AVector xs -> foldr S.union S.empty $ map processRec xs

        AUnary ALn x -> processRec x
        AUnary AFloor x -> processRec x
        AUnary ANeg x -> processRec x
        AUnary ANot x -> processRec x
        AUnary (AExp c) x -> processRec x
        AUnary (APower c) x -> processRec x

        ABinary ADiv x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AMult x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AAdd x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary ASub x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AMin x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AMax x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AAnd x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AOr  x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AXor x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary ALT x1 x2  -> S.union (processRec x1) (processRec x2)
        ABinary ALE x1 x2  -> S.union (processRec x1) (processRec x2)
        ABinary AEQ  x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AGE x1 x2  -> S.union (processRec x1) (processRec x2)
        ABinary AGT x1 x2  -> S.union (processRec x1) (processRec x2)
        ABinary AEQstr x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary ALTint x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary ALEint x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AEQint x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AGEint x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AGTint x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary ALike x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary ADistance x1 x2 -> S.union (processRec x1) (processRec x2)
    where processRec x = getAllSubExprs sensOnly x
          processBase x = S.singleton x

aexprToColSet :: (Show a, Ord a, Show b, Ord b) => M.Map a b -> Bool -> AExpr a -> S.Set b
aexprToColSet inputMap sensOnly aexpr = S.map (inputMap ! ) $ getAllAExprVars sensOnly aexpr

--------------------------
-- substitute variable subexpressions
aexprSubstitute :: (Ord a, Show a) => (M.Map a (AExpr a)) -> AExpr a -> AExpr a
aexprSubstitute aexprMap aexpr =
    case aexpr of
        AVar x -> processBase x
        AConst c -> AConst c
        AText c -> AText c

        ASubExpr t x g -> ASubExpr t x g
        AZeroSens x -> AZeroSens $ processRec x

        AAbs x -> AAbs $ processRec x
        ASum xs -> ASum $ map processRec xs
        AProd xs -> AProd $ map processRec xs
        AMins xs -> AMins $ map processRec xs
        AMaxs xs -> AMaxs $ map processRec xs
        AAnds xs -> AAnds $ map processRec xs
        AOrs  xs -> AOrs $ map processRec xs
        AXors xs -> AXors $ map processRec xs
        AVector xs -> AVector $ map processRec xs

        AUnary ALn x -> AUnary ALn $ processRec x
        AUnary AFloor x -> AUnary AFloor $ processRec x
        AUnary ANeg x -> AUnary ANeg $ processRec x
        AUnary ANot x -> AUnary ANot $ processRec x
        AUnary (AExp c) x -> AUnary (AExp c) $ processRec x
        AUnary (APower c) x -> AUnary (APower c) $ processRec x

        ABinary ADiv x1 x2 -> ABinary ADiv (processRec x1) (processRec x2)
        ABinary AMult x1 x2 -> ABinary AMult (processRec x1) (processRec x2)
        ABinary AAdd x1 x2 -> ABinary AAdd (processRec x1) (processRec x2)
        ABinary ASub x1 x2 -> ABinary ASub (processRec x1) (processRec x2)
        ABinary AMin x1 x2 -> ABinary AMin (processRec x1) (processRec x2)
        ABinary AMax x1 x2 -> ABinary AMax (processRec x1) (processRec x2)
        ABinary AAnd x1 x2 -> ABinary AAnd (processRec x1) (processRec x2)
        ABinary AOr  x1 x2 -> ABinary AOr (processRec x1) (processRec x2)
        ABinary AXor x1 x2 -> ABinary AXor (processRec x1) (processRec x2)
        ABinary ALT x1 x2  -> ABinary ALT (processRec x1) (processRec x2)
        ABinary ALE x1 x2  -> ABinary ALE (processRec x1) (processRec x2)
        ABinary AEQ  x1 x2 -> ABinary AEQ (processRec x1) (processRec x2)
        ABinary AGE x1 x2  -> ABinary AGE (processRec x1) (processRec x2)
        ABinary AGT x1 x2  -> ABinary AGT (processRec x1) (processRec x2)
        ABinary AEQstr x1 x2 -> ABinary AEQint (processRec x1) (processRec x2)
        ABinary ALTint x1 x2 -> ABinary ALTint (processRec x1) (processRec x2)
        ABinary ALEint x1 x2 -> ABinary ALEint (processRec x1) (processRec x2)
        ABinary AEQint x1 x2 -> ABinary AEQint (processRec x1) (processRec x2)
        ABinary AGEint x1 x2 -> ABinary AGEint (processRec x1) (processRec x2)
        ABinary AGTint x1 x2 -> ABinary AGTint (processRec x1) (processRec x2)
        ABinary ALike x1 x2 -> ABinary ALike (processRec x1) (processRec x2)
        ABinary ADistance x1 x2 -> ABinary ADistance (processRec x1) (processRec x2)
    where processRec x = aexprSubstitute aexprMap x
          processBase x = if M.member x aexprMap then aexprMap ! x else AVar x

-- TODO introduce type errors here
applyAexprTypes :: (M.Map VarName String) -> (AExpr VarName) -> (AType, AExpr VarName)
applyAexprTypes typeMap aexpr =
    case aexpr of
        AVar x   -> (stringToAType (typeMap ! x), AVar x)
        AConst c -> if isInteger c then (AInt, AConst c) else (AFloat, AConst c)
        AText c  -> (AString, AText c)

        ASubExpr t x g -> let v = preficedVarName t x in
                          if M.member v typeMap then (stringToAType (typeMap ! v), ASubExpr t x g)
                          else (AFloat, ASubExpr t x g)

        AZeroSens x  -> let (t,[y]) = processRec [x] in (t, AZeroSens y)

        AAbs x   -> let (t,[y]) = processRec [x] in (t, AAbs y)
        ASum xs  -> let (t,ys)  = processRec xs  in (t, ASum ys)
        AProd xs -> let (t,ys)  = processRec xs  in (t, AProd ys)
        AMins xs -> let (t,ys)  = processRec xs  in (t, AMins ys)
        AMaxs xs -> let (t,ys)  = processRec xs  in (t, AMaxs ys)
        AAnds xs -> let (t,ys)  = processRec xs  in (t, AAnds ys)
        AOrs  xs -> let (t,ys)  = processRec xs  in (t, AOrs ys)
        AXors xs -> let (t,ys)  = processRec xs  in (t, AXors ys)
        AVector xs -> let (t,ys)  = processRec xs  in (t, AVector ys)

        AUnary ALn x        -> let (_,[y]) = processRec [x] in (AFloat, AUnary ALn y)
        AUnary AFloor x     -> let (_,[y]) = processRec [x] in (AInt, AUnary AFloor y)
        AUnary ANeg x       -> let (t,[y]) = processRec [x] in (t, AUnary ANeg y)
        AUnary ANot x       -> let (t,[y]) = processRec [x] in (t, AUnary ANot y)
        AUnary (AExp c) x   -> let (t,[y]) = processRec [x] in (AFloat, AUnary (AExp c) y)
        AUnary (APower c) x -> let (t,[y]) = processRec [x] in
                                   if isInteger c && c >= 0 then
                                       (t, AUnary (APower c) y)
                                   else
                                       (AFloat, AUnary (APower c) y)

        ABinary ADiv x1 x2  -> let (t,[y1,y2]) = processRec [x1,x2]  in (AFloat, ABinary ADiv y1 y2)
        ABinary AMult x1 x2 -> let (t,[y1,y2]) = processRec [x1,x2]  in (t, ABinary AMult y1 y2)
        ABinary AAdd x1 x2 -> let (t,[y1,y2]) = processRec [x1,x2]  in (t, ABinary AAdd y1 y2)
        ABinary ASub x1 x2 -> let (t,[y1,y2]) = processRec [x1,x2]  in (t, ABinary ASub y1 y2)
        ABinary AMin x1 x2 -> let (t,[y1,y2]) = processRec [x1,x2]  in (t, ABinary AMin y1 y2)
        ABinary AMax x1 x2 -> let (t,[y1,y2]) = processRec [x1,x2]  in (t, ABinary AMax y1 y2)
        ABinary AAnd x1 x2 -> let (t,[y1,y2]) = processRec [x1,x2]  in (t, ABinary AAnd y1 y2)
        ABinary AOr  x1 x2 -> let (t,[y1,y2]) = processRec [x1,x2]  in (t, ABinary AOr y1 y2)
        ABinary AXor x1 x2 -> let (t,[y1,y2]) = processRec [x1,x2]  in (t, ABinary AXor y1 y2)
        ABinary ALT x1 x2  -> let (t,[y1,y2]) = processRec [x1,x2]  in
                                  case t of
                                      AInt -> (ABool, ABinary ALTint y1 y2)
                                      _    -> (ABool, ABinary ALT y1 y2)
        ABinary ALE x1 x2  -> let (t,[y1,y2]) = processRec [x1,x2]  in
                                  case t of
                                      AInt -> (ABool, ABinary ALEint y1 y2)
                                      _    -> (ABool, ABinary ALE y1 y2)
        ABinary AEQ  x1 x2 -> let (t,[y1,y2]) = processRec [x1,x2]  in
                                  case t of
                                      AInt    -> (ABool, ABinary AEQint y1 y2)
                                      AString -> (ABool, ABinary AEQstr y1 y2)
                                      _       -> (ABool, ABinary AEQ y1 y2)
        ABinary AGE x1 x2  -> let (t,[y1,y2]) = processRec [x1,x2]  in
                                  case t of
                                      AInt -> (ABool, ABinary AGEint y1 y2)
                                      _    -> (ABool, ABinary AGE y1 y2)
        ABinary AGT x1 x2  -> let (t,[y1,y2]) = processRec [x1,x2]  in
                                  case t of
                                      AInt -> (ABool, ABinary AGTint y1 y2)
                                      _    -> (ABool, ABinary AGT y1 y2)

        -- forced type conversions
        ABinary ALTint x1 x2 -> let (t,[y1,y2]) = processRec [x1,x2]  in (AInt, ABinary ALTint y1 y2)
        ABinary ALEint x1 x2 -> let (t,[y1,y2]) = processRec [x1,x2]  in (AInt, ABinary ALEint y1 y2)
        ABinary AEQint x1 x2 -> let (t,[y1,y2]) = processRec [x1,x2]  in (AInt, ABinary AEQint y1 y2)
        ABinary AGEint x1 x2 -> let (t,[y1,y2]) = processRec [x1,x2]  in (AInt, ABinary AGEint y1 y2)
        ABinary AGTint x1 x2 -> let (t,[y1,y2]) = processRec [x1,x2]  in (AInt, ABinary AGTint y1 y2)

        ABinary AEQstr x1 x2 -> let (t,[y1,y2]) = processRec [x1,x2]  in (AString, ABinary AEQstr y1 y2)
        ABinary ALike x1 x2  -> let (t,[y1,y2]) = processRec [x1,x2]  in (AString, ABinary ALike y1 y2)
        ABinary ADistance x1 x2  -> let (t,[y1,y2]) = processRec [x1,x2]  in (AString, ABinary ADistance y1 y2)
   where processRec xs =
             let (types,aexprs) = unzip (map (applyAexprTypes typeMap) xs) in
             (foldr max AUnit types, aexprs)
         isInteger c = (ceiling c == floor c)



---------------------------------------------------------------------------------------------------
-- symbolic execution of intervals

-- TODO if the sensitive variable is in a non-sensitive row, we may also consider its exact value

aexprRange :: M.Map String String -> M.Map String String -> M.Map String (VState (AExpr String)) -> S.Set VarName -> AExpr String
              -> VState (AExpr String)
aexprRange subTableAliasMap typeMap attMap sensVars aexpr =

    case aexpr of

        -- we look for known constraints in attMap, and if it is not there, use the typeMap
        -- TODO attMap contains tableNames while typeMap and sensVars contain aliases!
        AVar x   -> let v = queryNameToVarName x in
                    if not (S.member v sensVars) then Range (AVar x) (AVar x)
                    else if M.member v attMap then attMap ! v
                    else case typeMap ! v of
                             "int"  -> Range (AConst (-2^32)) (AConst (2^32))
                             "bool" -> Range (AConst 0) (AConst 1)
                             _      -> unknown

        AConst c -> Range (AConst c) (AConst c)
        AText c  -> unknown

        -- the outputs of intermediate tables are treated similarly to input vars,
        -- since intermediate table schema is optional, it is possible that the variable is not present in typeMap
        -- TODO we need composition here
        ASubExpr t x _ -> let t0 = if M.member t subTableAliasMap then subTableAliasMap ! t else t in
                          let v0 = preficedVarName t0 x in
                          let v  = preficedVarName t  x in
                          if not (S.member v sensVars) then Range (AVar x) (AVar x)
                          else if M.member v0 attMap then attMap ! v0
                          else if M.member v typeMap then
                              case typeMap ! v of
                                  "int"  -> Range (AConst (-2^32)) (AConst (2^32))
                                  "bool" -> Range (AConst 0) (AConst 1)
                                  _      -> unknown
                          else
                              unknown

        AZeroSens x  -> processRec x
        AAbs x       -> let y = processRec x in rangeAbsPoly zero fabs fle fmul fmin fmax y

        ASum xs  -> let ys = map processRec xs in rangeSumPoly fadd ys
        AProd xs -> let ys = map processRec xs in rangeProductPoly fmul fmins fmaxs ys
        AMins xs -> let ys = map processRec xs in rangeMinsPoly fmin ys
        AMaxs xs -> let ys = map processRec xs in rangeMaxsPoly fmax ys
        AAnds xs -> let ys = map processRec xs in rangeAndsPoly fmin ys
        AOrs  xs -> let ys = map processRec xs in rangeOrsPoly fmax ys
        AXors xs -> let ys = map processRec xs in rangeXorsPoly fxor fmin fmax ys

        AUnary ALn x        -> let y = processRec x in rangeMonotonePoly (AUnary ALn) y
        AUnary AFloor x     -> processRec x
        AUnary ANeg x       -> let y = processRec x in rangeNegPoly fneg y
        AUnary ANot x       -> let y = processRec x in rangeNotPoly fnot y
        AUnary (AExp c) x   -> let y = processRec x in rangeMonotonePoly (AUnary (AExp c)) y
        AUnary (APower c) x -> let y = processRec x in rangeMonotonePoly (AUnary (APower c)) y

        ABinary ADiv x1 x2  -> let y1 = processRec x1 in
                               let y2 = processRec x2 in
                               rangeDivPoly fdiv fmins fmaxs y1 y2
        ABinary AMult x1 x2 -> let y1 = processRec x1 in
                               let y2 = processRec x2 in
                               rangeMulPoly fmul fmins fmaxs y1 y2
        ABinary AAdd x1 x2  -> let y1 = processRec x1 in
                               let y2 = processRec x2 in
                               rangeAddPoly fadd y1 y2
        ABinary ASub x1 x2  -> let y1 = processRec x1 in
                               let y2 = processRec x2 in
                               rangeSubPoly fadd fneg y1 y2
        ABinary AMin x1 x2  -> let y1 = processRec x1 in
                               let y2 = processRec x2 in
                               rangeMinPoly fmin y1 y2
        ABinary AMax x1 x2  -> let y1 = processRec x1 in
                               let y2 = processRec x2 in
                               rangeMaxPoly fmax y1 y2
        ABinary AAnd x1 x2  -> let y1 = processRec x1 in
                               let y2 = processRec x2 in
                               rangeMinPoly fmin y1 y2
        ABinary AOr  x1 x2  -> let y1 = processRec x1 in
                               let y2 = processRec x2 in
                               rangeMaxPoly fmax y1 y2
        ABinary AXor x1 x2  -> let y1 = processRec x1 in
                               let y2 = processRec x2 in
                               rangeXorPoly fxor fmin fmax y1 y2

        ABinary ALT x1 x2   -> let y1 = processRec x1 in
                               let y2 = processRec x2 in
                               rangeLTPoly flt y1 y2
        ABinary ALE x1 x2   -> let y1 = processRec x1 in
                               let y2 = processRec x2 in
                               rangeLEPoly fle y1 y2
        ABinary AEQ  x1 x2  -> let y1 = processRec x1 in
                               let y2 = processRec x2 in
                               rangeOrPoly fmax (rangeLEPoly fle y1 y2) (rangeLEPoly fle y2 y1)
        ABinary AGE x1 x2   -> let y1 = processRec x1 in
                               let y2 = processRec x2 in
                               rangeLEPoly fle y2 y1
        ABinary AGT x1 x2   -> let y1 = processRec x1 in
                               let y2 = processRec x2 in
                               rangeLTPoly flt y2 y1

        ABinary ALTint x1 x2 -> let y1 = processRec x1 in
                                let y2 = processRec x2 in
                                rangeLTPoly flt y1 y2
        ABinary ALEint x1 x2 -> let y1 = processRec x1 in
                                let y2 = processRec x2 in
                                rangeLEPoly fle y1 y2
        ABinary AEQint x1 x2 -> let y1 = processRec x1 in
                                let y2 = processRec x2 in
                                rangeOrPoly fmax (rangeLEPoly fle y1 y2) (rangeLEPoly fle y2 y1)
        ABinary AGEint x1 x2 -> let y1 = processRec x1 in
                                let y2 = processRec x2 in
                                rangeLEPoly fle y2 y1
        ABinary AGTint x1 x2 -> let y1 = processRec x1 in
                                let y2 = processRec x2 in
                                rangeLTPoly flt y2 y1

        ABinary AEQstr x1 x2 -> let y1 = processRec x1 in
                                let y2 = processRec x2 in
                                rangeOrPoly fmax (rangeLEPoly fle y1 y2) (rangeLEPoly fle y2 y1)
        ABinary ALike x1 x2  -> let y1 = processRec x1 in
                                let y2 = processRec x2 in
                                rangeOrPoly fmax (rangeLEPoly fle y1 y2) (rangeLEPoly fle y2 y1)

        ABinary ADistance (AVector xs1) (AVector xs2) ->
                                let ys1 = map processRec xs1 in
                                let ys2 = map processRec xs2 in
                                let ys  = map (rangeAbsPoly zero fabs fle fmul fmin fmax) $ zipWith (rangeSubPoly fadd fneg) ys1 ys2 in
                                rangeLpNormPoly 2 inf ninf zero fabs fle fmul fmin fmax aexprLpnorm ys

        _                        -> error $ error_badRangeAexpr aexpr

   where unknown = Range ninf inf
         fadd = ABinary AAdd
         fdiv = ABinary ADiv
         fmul = ABinary AMult
         fxor = ABinary AXor
         fle  = ABinary ALE
         flt  = ABinary ALT
         fmin = ABinary AMin
         fmax = ABinary AMax

         fneg = AUnary ANeg
         fnot = AUnary ANot

         fmins = AMins
         fmaxs = AMaxs
         fabs  = AAbs

         zero = AConst 0
         ninf = AConst (-99999.99)
         inf  = AConst 99999.99

         processRec = aexprRange subTableAliasMap typeMap attMap sensVars

