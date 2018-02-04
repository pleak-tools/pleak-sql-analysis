module Aexpr where

import Data.List
import Data.Map
import Debug.Trace
import Expr

-- we want to parse complex expressions and transform them to Expr afterwards
data AExpr a
  = AVar a
  | AConst Double
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
  | ALn | ANeg
  | AExp   Double
  | ARoot  Double
  | APower Double
  deriving (Show)

data ABinOp
  = ADiv | AMult | AAdd | ASub | AMin | AMax
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
                (ASum xs, ASum ys) -> ASum (xs ++ (Data.List.map (AUnary ANeg) ys))
                (ASum xs, _      ) -> ASum ((AUnary ANeg y'):xs)
                (_      , ASum ys) -> ASum (x':(Data.List.map (AUnary ANeg) ys))
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
                (AProd xs, AProd ys) -> AProd (xs ++ (Data.List.map (\v -> AUnary (APower (-1.0)) (AUnary ALn v) ) ys))
                (AProd xs, _       ) -> AProd ((AUnary (APower (-1.0)) (AUnary ALn y')):xs)
                (_       , AProd ys) -> AProd (x':(Data.List.map (\v -> AUnary (APower (-1.0)) (AUnary ALn v)) ys))
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

aexprNormalize (AUnary AAbsEnd (AUnary AAbsBegin x)) = AAbs (aexprNormalize x)

aexprNormalize (AUnary f x) = AUnary f (aexprNormalize x)
-- TODO all binary expressions have already been considered as special cases, but we will probably need this later
-- aexprNormalize (ABinary f x y) = ABinary f (aexprNormalize x) (aexprNormalize y)
aexprNormalize x = x

-- we do not convert sigmoids since they come only from filters
-- we do not convert aggregation since it comes separately
-- we do not convert scaleNorm and zeroSens since they come from the database norm
aexprToExpr :: VarName -> AExpr VarName -> (Map VarName Expr)
aexprToExpr y (AUnary (APower c) (AVar x))              = fromList [(y, Power x c)]
aexprToExpr y (AUnary (APower c) (AUnary ALn (AVar x))) = fromList [(y, PowerLN x c)]
aexprToExpr y (AUnary (APower c) x) = 
    let z = y ++ "~1" in
    Data.Map.union (fromList [(y, Power z c)]) (aexprToExpr z x)

aexprToExpr y (AUnary (AExp c) (AVar x)) = fromList [(y, Exp c x)]
aexprToExpr y (AUnary (AExp c) x) = 
    let z = y ++ "~1" in
    Data.Map.union (fromList [(y, Exp c z)]) (aexprToExpr z x)

aexprToExpr y (AUnary ANeg (AConst c)) = fromList [(y, Const (-c))]
aexprToExpr y (AUnary ANeg x) =
    let z      = y ++ "~1" in
    let oneNeg = "-1" in
    Data.Map.union (fromList [(y, Prod [oneNeg, z]), (oneNeg, Const (-1.0))]) (aexprToExpr z x)

aexprToExpr y (AUnary ALn  (AConst c)) = fromList [(y, Const (log c))]
aexprToExpr y (AConst c) = fromList [(y, Const c)]
aexprToExpr y (AVar x)   = fromList [(y, Id x)]

-- lp-norm
aexprToExpr y aexpr@(AUnary (ARoot p) (ASum xs)) =

    -- collect all expression and variable arguments separately
    let ysExpr = Data.List.filter (\x -> case x of {AUnary (APower q) (AAbs _)        -> if p == q then True else False; _ -> False}) xs in
    let ysVar  = Data.List.filter (\x -> case x of {AUnary (APower q) (AAbs (AVar _)) -> if p == q then True else False; _ -> False}) xs in

        -- if all arguments are p-powers of absolute values, then we have an lp-norm
        if (length xs == length ysExpr) then

            -- if there is at least one expression argument that is not a variable, convert all variables to expressions as x~ = Power x 1.0
            if (length ysVar < length ysExpr) then
                let zs = Data.List.map (\x -> y ++ "~" ++ show x) [1..length xs] in
                let ws = Data.List.map (\(x,z) -> case x of AUnary (APower _) (AAbs x') -> aexprToExpr z x') (zip xs zs) in
                Data.Map.union (fromList [(y, L p zs)]) $ Data.List.foldr Data.Map.union Data.Map.empty ws

            -- otherwise, take the variables directly
            else
                let zs = Data.List.map (\x -> case x of {AUnary (APower _) (AAbs (AVar z)) -> z}) xs in
                fromList[(y, L p zs)]

        -- otherwise, we fail since we do not know how to compute root sensitivities yet
        else error ("could not interpret the expression " ++ show aexpr)

aexprToExpr y aexpr@(AUnary (ARoot p) (AUnary (APower q) (AAbs (AVar x)))) =
    if p == q then
        fromList [(y, L p [x])]
    else error ("could not interpret the expression " ++ show aexpr)

aexprToExpr y aexpr@(AUnary (ARoot p) (AUnary (APower q) (AAbs x))) =
    if p == q then
        let z = y ++ "~1" in
        Data.Map.union (fromList [(y, L p [z])]) (aexprToExpr z x)
    else error ("could not interpret the expression " ++ show aexpr)

-- l1-norm and sum
aexprToExpr y aexpr@(ASum xs) =

    -- collect all expression and variable arguments separately
    let ysExpr = Data.List.filter (\x -> case x of {AAbs _        -> True; _ -> False}) xs in
    let ysVar  = Data.List.filter (\x -> case x of {AAbs (AVar _) -> True; _ -> False}) xs in

        -- if all arguments are absolute values, then we have an l1-norm
        if (length xs == length ysExpr) then

            -- if there is at least one expression argument that is not a variable, convert all variables to expressions as z~ = Power z 1.0
            if (length ysVar < length ysExpr) then
                let zs = Data.List.map (\x -> y ++ "~" ++ show x) [1..length xs] in
                let ws = Data.List.map (\(x,z) -> case x of AAbs x' -> aexprToExpr z x') (zip xs zs) in
                Data.Map.union (fromList [(y, L 1.0 zs)]) $ Data.List.foldr Data.Map.union Data.Map.empty ws

            -- otherwise, take the variables directly
            else
                let zs = Data.List.map (\x -> case x of {AAbs (AVar z) -> z}) xs in
                fromList[(y, L 1.0 zs)]

            -- otherwise, we have a sum
            else
                    let zs = Data.List.map (\x -> y ++ "~" ++ show x) [1..length xs] in
                    let ws = Data.List.map (\(x,z) -> aexprToExpr z x) (zip xs zs) in
                    Data.Map.union (fromList [(y, Sum zs)]) $ Data.List.foldr Data.Map.union Data.Map.empty ws

aexprToExpr y (AAbs (AVar x)) = fromList [(y, L 1.0 [x])]

aexprToExpr y (AAbs x) =
    let z = y ++ "~1" in
    Data.Map.union (fromList [(y, L 1.0 [z])]) (aexprToExpr z x)

-- linf-norm
aexprToExpr y (AMaxs xs) =

            -- if all arguments are absolute values, then we have an linf-norm
            let ys = Data.List.filter (\x -> case x of {AAbs (AVar _) -> True; _ -> False}) xs in
            if length ys == length xs then
                        let zs = Data.List.map (\x -> case x of AAbs (AVar x') -> x') xs in
                        fromList[(y, LInf zs)]

            -- otherwise, we have a max
            else
                let zs = Data.List.map (\x -> y ++ "~" ++ show x) [1..length xs] in
                let ws = Data.List.map (\(x,z) -> aexprToExpr z x) (zip xs zs) in
                Data.Map.union (fromList [(y, Max zs)]) $ Data.List.foldr Data.Map.union Data.Map.empty ws

aexprToExpr y (AMins xs) =
    let zs = Data.List.map (\x -> y ++ "~" ++ show x) [1..length xs] in
    let ws = Data.List.map (\(x,z) -> aexprToExpr z x) (zip xs zs) in
    Data.Map.union (fromList [(y, Min zs)]) $ Data.List.foldr Data.Map.union Data.Map.empty ws

aexprToExpr y (AProd xs) =
    let zs = Data.List.map (\x -> y ++ "~" ++ show x) [1..length xs] in
    let ws = Data.List.map (\(x,z) -> aexprToExpr z x) (zip xs zs) in
    Data.Map.union (fromList [(y, Prod zs)]) $ Data.List.foldr Data.Map.union Data.Map.empty ws

-- we may possibly add more interesting expressions that can be reduced to Expr
aexprToExpr y aexpr = error ("could not interpret " ++ show aexpr)

