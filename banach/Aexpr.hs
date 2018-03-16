module Aexpr where

import Data.List
import qualified Data.Map as M

import ErrorMsg
import Expr

-- the default value for Tauoids, b makes them precise, and ScaleNorm maps b back to a
a = 0.1
b = 10.0

-- we want to parse complex expressions and transform them to Expr afterwards
data AExpr a
  = AVar a
  | AConst Double
  | ASubExpr Expr
  | AUnary  AUnOp (AExpr a)
  | ABinary ABinOp (AExpr a) (AExpr a)
  | AAbs  (AExpr a)
  | ASum  [AExpr a]
  | AProd [AExpr a]
  | AMins [AExpr a]
  | AMaxs [AExpr a]
  deriving (Show)

data AUnOp
  = AAbsBegin | AAbsEnd 
  | ALn | ANeg | ANot
  | AExp   Double
  | APower Double
  deriving (Show)

data ABinOp
  = ADiv | AMult | AAdd | ASub | AMin | AMax | AAnd | AOr | ALT | AEQ | AGT
  deriving (Show)


-- some normalization to simplify the transformation
aexprNormalize :: AExpr a -> AExpr a
aexprNormalize (ABinary AAdd x y) = 
            let x' = aexprNormalize x in
            let y' = aexprNormalize y in
            case (x',y') of
                (ASum xs, ASum ys) -> ASum (xs ++ ys)
                (ASum xs, _      ) -> ASum (y':xs)
                (_      , ASum ys) -> ASum (x':ys)
                (_      , _      ) -> ASum [x',y']

aexprNormalize (ABinary ASub x y) = 
            let x' = aexprNormalize x in
            let y' = aexprNormalize y in
            case (x',y') of
                (ASum xs, ASum ys) -> ASum (xs ++ map (AUnary ANeg) ys)
                (ASum xs, _      ) -> ASum ((AUnary ANeg y'):xs)
                (_      , ASum ys) -> ASum (x': map (AUnary ANeg) ys)
                (_      , _      )  -> ASum [x',AUnary ANeg y']

aexprNormalize (ABinary AMult x y) = 
            let x' = aexprNormalize x in
            let y' = aexprNormalize y in
            case (x',y') of
                (AProd xs, AProd ys) -> AProd (xs ++ ys)
                (AProd xs, _       ) -> AProd (y':xs)
                (_       , AProd ys) -> AProd (x':ys)
                (_       , _       ) -> AProd [x',y']

aexprNormalize (ABinary ADiv x y) = 
            let x' = aexprNormalize x in
            let y' = aexprNormalize y in
            case (x',y') of
                (AProd xs, AProd ys) -> AProd (xs ++ map (\v -> AUnary (APower (-1.0)) (AUnary ALn v) ) ys)
                (AProd xs, _       ) -> AProd ((AUnary (APower (-1.0)) (AUnary ALn y')):xs)
                (_       , AProd ys) -> AProd (x': map (\v -> AUnary (APower (-1.0)) (AUnary ALn v)) ys)
                (_       , _       ) -> AProd [x',AUnary (APower (-1.0)) (AUnary ALn y')]

aexprNormalize (ABinary AMin x y) = 
            let x' = aexprNormalize x in
            let y' = aexprNormalize y in
            case (x',y') of
                (AMins xs, AMins ys) -> AMins (xs ++ ys)
                (AMins xs, _       ) -> AMins (y':xs)
                (_       , AMins ys) -> AMins (x':ys)
                (_       , _       ) -> AMins [x',y']

aexprNormalize (ABinary AMax x y) = 
            let x' = aexprNormalize x in
            let y' = aexprNormalize y in
            case (x',y') of
                (AMaxs xs, AMaxs ys) -> AMaxs (xs ++ ys)
                (AMaxs xs, _       ) -> AMaxs (y':xs)
                (_       , AMaxs ys) -> AMaxs (x':ys)
                (_       , _       ) -> AMaxs [x',y']

aexprNormalize (ABinary AAnd x y) = aexprNormalize $ ABinary AMult x y
aexprNormalize (ABinary AOr x y) = aexprNormalize $ ABinary ASub (ABinary AAdd x y) (ABinary AMult x y)

aexprNormalize (AUnary AAbsEnd (AUnary AAbsBegin x)) = AAbs (aexprNormalize x)

aexprNormalize (AUnary f x) = AUnary f (aexprNormalize x)
aexprNormalize (ABinary f x y) = ABinary f (aexprNormalize x) (aexprNormalize y)
aexprNormalize x = x

-- we do not convert sigmoids since they come only from filters
-- we do not convert aggregation since it comes separately
-- we do not convert scaleNorm and zeroSens since they come from the database norm
aexprToExpr :: VarName -> AExpr VarName -> (M.Map VarName Expr)

aexprToExpr y (AUnary (AExp c) (AVar x)) = M.fromList [(y, Exp c x)]
aexprToExpr y (AUnary (AExp c) x) = 
    let z = y ++ "~1" in
    M.union (M.fromList [(y, Exp c z)]) (aexprToExpr z x)

aexprToExpr y (AUnary ANeg (AConst c)) = M.fromList [(y, Const (-c))]
aexprToExpr y (AUnary ANeg x) =
    let z      = y ++ "~1" in
    let oneNeg = "-1" in
    M.union (M.fromList [(y, Prod [oneNeg, z]), (oneNeg, Const (-1.0))]) (aexprToExpr z x)

aexprToExpr y (AUnary ANot x) = 
    let z      = y ++ "~1" in
    let oneNeg = "-1" in
    M.union (M.fromList [(y, Prod [oneNeg, z]), (oneNeg, Const (-1.0))]) (aexprToExpr z x)

aexprToExpr y (AUnary ALn  (AConst c)) = M.fromList [(y, Const (log c))]
aexprToExpr y (AConst c)   = M.fromList [(y, Const c)]
aexprToExpr y (AVar x)     = M.fromList [(y, Id x)]
aexprToExpr y (ASubExpr e) = M.fromList [(y, e)]

aexprToExpr y (ABinary ALT x (AConst c)) = 
    let z      = y ++ "~0" in
    let z1     = y ++ "~1" in
    let w1     = y ++ "~2" in
    let w2     = y ++ "~3" in
    let one = "1" in
    let oneNeg = "-1" in
    M.union (aexprToExpr z x) $ M.fromList [(y, Sum [one,w2]), (w2, Prod [oneNeg,w1]), (w1, Sigmoid a c z), (one, Const (1.0)), (oneNeg, Const (-1.0))]

aexprToExpr y (ABinary ALT x1 x2) = 
    let z       = y ++ "~0" in 
    let z1      = y ++ "~1" in
    let z2      = y ++ "~2" in
    let w1      = y ++ "~3" in
    let w2      = y ++ "~4" in
    let oneNeg = "-1" in
    M.union (aexprToExpr z1 x1) $ M.union (aexprToExpr z2 x2) $ M.fromList [(y, Sigmoid a 0.0 z), (z, Sum [z2,w1]), (w1, Prod [oneNeg,z1]), (oneNeg, Const (-1.0))]

aexprToExpr y (ABinary AEQ x (AConst c)) = 
    let z      = y ++ "~0" in
    let z1     = y ++ "~1" in
    M.union (aexprToExpr z x) $ M.fromList [(y, Tauoid a c z)]

aexprToExpr y (ABinary AEQ x1 x2) = 
    let z      = y ++ "~0" in 
    let z1     = y ++ "~1" in
    let z2     = y ++ "~2" in
    let w1     = y ++ "~3" in
    let w2     = y ++ "~4" in
    let oneNeg = "-1" in
    M.union (aexprToExpr z1 x1) $ M.union (aexprToExpr z2 x2) $ M.fromList [(y, Tauoid a 0.0 z), (z, Sum [z1,w1]), (w1, Prod [oneNeg,z2]), (oneNeg, Const (-1.0))]

aexprToExpr y (ABinary AGT x (AConst c)) = 
    let z      = y ++ "~0" in
    let z1     = y ++ "~1" in
    M.union (aexprToExpr z x) $ M.fromList [(y, Sigmoid a c z)]

aexprToExpr y (ABinary AGT x1 x2) = 
    let z       = y ++ "~0" in 
    let z1      = y ++ "~1" in
    let z2      = y ++ "~2" in
    let w1     = y ++ "~3" in
    let w2     = y ++ "~4" in
    let oneNeg = "-1" in
    M.union (aexprToExpr z1 x1) $ M.union (aexprToExpr z2 x2) $ M.fromList [(y, Sigmoid a 0.0 z), (z, Sum [z1,w1]), (w1, Prod [oneNeg,z2]), (oneNeg, Const (-1.0))]

-- lp-norm
aexprToExpr y aexpr@(AUnary (APower pinv) (ASum xs)) =

    let p = 1 / pinv in

    -- if p is an even number, we do not need to take absolute value of the arguments
    let pint = round p in
    let isEven = mod pint 2 == 0 && p == fromIntegral pint in

    -- collect all expression and variable arguments separately
    let ysExpr = filter (\x -> case x of {AUnary (APower q) (AAbs _)        -> p == q; AUnary (APower q) _        -> p == q && isEven; _ -> False}) xs in
    let ysVar  = filter (\x -> case x of {AUnary (APower q) (AAbs (AVar _)) -> p == q; AUnary (APower q) (AVar _) -> p == q && isEven; _ -> False}) xs in

        -- if all arguments are p-powers of absolute values, then we have an lp-norm
        if (length xs == length ysExpr) then

            -- if there is at least one expression argument that is not a variable, convert all variables to expressions as x~ = Power x 1.0
            if (length ysVar < length ysExpr) then
                let zs = map (\x -> y ++ "~" ++ show x) [1..length xs] in
                let ws = map (\(x,z) -> case x of {AUnary (APower _) (AAbs x') -> aexprToExpr z x'; AUnary (APower _) x' -> aexprToExpr z x'}) (zip xs zs) in
                M.union (M.fromList [(y, L p zs)]) $ foldr M.union M.empty ws

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
        let z = y ++ "~1" in
        M.union (M.fromList [(y, L p [z])]) (aexprToExpr z x)
    else error $ error_queryExpr aexpr

aexprToExpr y aexpr@(AUnary (APower pinv) (AUnary (APower q) (AVar x))) =

    -- if p is an even number, we do not need to take absolute value of the arguments
    let p = 1 / pinv in
    let pint = round p in
    let isEven = mod pint 2 == 0 && p == fromIntegral pint in
    if p == q && isEven then
        M.fromList [(y, L p [x])]
    else error $ error_queryExpr aexpr

aexprToExpr y aexpr@(AUnary (APower pinv) (AUnary (APower q) x)) =

    -- if p is an even number, we do not need to take absolute value of the arguments
    let p = 1 / pinv in
    let pint = round p in
    let isEven = mod pint 2 == 0 && p == fromIntegral pint in
    if p == q && isEven then
        let z = y ++ "~1" in
        M.union (M.fromList [(y, L p [z])]) (aexprToExpr z x)
    else error $ error_queryExpr aexpr

aexprToExpr y (AUnary (APower c) (AVar x))              = M.fromList [(y, Power x c)]
aexprToExpr y (AUnary (APower c) (AUnary ALn (AVar x))) = M.fromList [(y, PowerLN x c)]
aexprToExpr y (AUnary (APower c) x) = 
    let z = y ++ "~1" in
    M.union (M.fromList [(y, Power z c)]) (aexprToExpr z x)

-- l1-norm and sum
aexprToExpr y aexpr@(ASum xs) =

    -- collect all expression and variable arguments separately
    let ysExpr = filter (\x -> case x of {AAbs _        -> True; _ -> False}) xs in
    let ysVar  = filter (\x -> case x of {AAbs (AVar _) -> True; _ -> False}) xs in

        -- if all arguments are absolute values, then we have an l1-norm
        if (length xs == length ysExpr) then

            -- if there is at least one expression argument that is not a variable, convert all variables to expressions as z~ = Power z 1.0
            if (length ysVar < length ysExpr) then
                let zs = map (\x -> y ++ "~" ++ show x) [1..length xs] in
                let ws = map (\(x,z) -> case x of AAbs x' -> aexprToExpr z x') (zip xs zs) in
                M.union (M.fromList [(y, L 1.0 zs)]) $ foldr M.union M.empty ws

            -- otherwise, take the variables directly
            else
                let zs = map (\x -> case x of {AAbs (AVar z) -> z}) xs in
                M.fromList[(y, L 1.0 zs)]

            -- otherwise, we have a sum
            else
                    let zs = map (\x -> y ++ "~" ++ show x) [1..length xs] in
                    let ws = map (\(x,z) -> aexprToExpr z x) (zip xs zs) in
                    M.union (M.fromList [(y, Sum zs)]) $ foldr M.union M.empty ws

aexprToExpr y (AAbs (AVar x)) = M.fromList [(y, L 1.0 [x])]

aexprToExpr y (AAbs x) =
    let z = y ++ "~1" in
    M.union (M.fromList [(y, L 1.0 [z])]) (aexprToExpr z x)

-- linf-norm
aexprToExpr y (AMaxs xs) =

            -- if all arguments are absolute values, then we have an linf-norm
            let ys = filter (\x -> case x of {AAbs (AVar _) -> True; _ -> False}) xs in
            if length ys == length xs then
                        let zs = map (\x -> case x of AAbs (AVar x') -> x') xs in
                        M.fromList[(y, LInf zs)]

            -- otherwise, we have a max
            else
                let zs = map (\x -> y ++ "~" ++ show x) [1..length xs] in
                let ws = map (\(x,z) -> aexprToExpr z x) (zip xs zs) in
                M.union (M.fromList [(y, Max zs)]) $ foldr M.union M.empty ws

aexprToExpr y (AMins xs) =
    let zs = map (\x -> y ++ "~" ++ show x) [1..length xs] in
    let ws = map (\(x,z) -> aexprToExpr z x) (zip xs zs) in
    M.union (M.fromList [(y, Min zs)]) $ foldr M.union M.empty ws

aexprToExpr y (AProd xs) =
    let zs = map (\x -> y ++ "~" ++ show x) [1..length xs] in
    let ws = map (\(x,z) -> aexprToExpr z x) (zip xs zs) in
    M.union (M.fromList [(y, Prod zs)]) $ foldr M.union M.empty ws

-- we may possibly add more interesting expressions that can be reduced to Expr
aexprToExpr y aexpr = error $ error_queryExpr aexpr

