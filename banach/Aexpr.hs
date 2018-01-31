module Aexpr where

import Data.List
import Data.Map
import Debug.Trace

-- import Expr from Banach.hs
import qualified Banach as B
import Expr

-- we want to parse complex expressions and transform them to Expr afterwards
data AExpr a
  = Var a
  | IntConst Integer
  | AUnary  AUnOp (AExpr a)
  | ABinary ABinOp (AExpr a) (AExpr a)
  | AAbs  (AExpr a)
  | ASum  [AExpr a]
  | AProd [AExpr a]
  | AMins [AExpr a]
  | AMaxs [AExpr a]
  deriving (Show)

data AUnOp
  = ALn | AAbsBegin | AAbsEnd | ANeg
  | AScale Double 
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
--aexprNormalize (ABinary f x y) = ABinary f (aexprNormalize x) (aexprNormalize y)
aexprNormalize x = x

aexprToExpr :: VarName -> AExpr VarName -> (Map VarName Expr)
aexprToExpr y (AUnary (APower c) (Var x))              = fromList [(y, Power x c)]
aexprToExpr y (AUnary (APower c) (AUnary ALn (Var x))) = fromList [(y, PowerLN x c)]
aexprToExpr y (AUnary (APower c) x) = 
    let z = y ++ "~1" in
    Data.Map.union (fromList [(y, Power z c)]) (aexprToExpr z x)

aexprToExpr y (AUnary (AExp c) (Var x)) = fromList [(y, Exp c x)]

-- lp-norm
aexprToExpr y aexpr@(AUnary (ARoot p) (ASum xs)) =

            let ys1 = Data.List.filter (\x -> case x of {AUnary (APower q) (AAbs _)       -> if p == q then True else False; _ -> False}) xs in
            let ys2 = Data.List.filter (\x -> case x of {AUnary (APower q) (AAbs (Var _)) -> if p == q then True else False; _ -> False}) xs in

            if (length xs == length ys1) && (length ys2 == 0 || length ys2 == length ys1) then

                    if length ys2 == 0 then
                        let zs = Data.List.map (\x -> y ++ "~" ++ show x) [1..length xs - 1] in
                        let ws  = Data.List.map (\(x,w) -> case x of {AUnary (APower q) (AAbs z) -> aexprToExpr w z}) (zip xs zs) in
                        Data.Map.union (fromList [(y, L p zs)]) $ Data.List.foldr Data.Map.union Data.Map.empty ws
                    else
                        let zs = Data.List.map (\x -> case x of {AUnary (APower q) (AAbs (Var z)) -> z}) xs in
                        fromList[(y, L p zs)]
            else
                error ("could not interpret the expression " ++ show aexpr)

-- l1-norm
aexprToExpr y aexpr@(ASum xs) =

            let ys1 = Data.List.filter (\x -> case x of {AAbs _       -> True; _ -> False}) xs in
            let ys2 = Data.List.filter (\x -> case x of {AAbs (Var _) -> True; _ -> False}) xs in

            if (length xs == length ys1) && (length ys2 == 0 || length ys2 == length ys1) then

                    if length ys2 == 0 then
                        let zs = Data.List.map (\x -> y ++ "~" ++ show x) [1..length xs] in
                        let ws  = Data.List.map (\(x,z) -> case x of {AAbs x' -> aexprToExpr z x'}) (zip xs zs) in
                        Data.Map.union (fromList [(y, L 1.0 zs)]) $ Data.List.foldr Data.Map.union Data.Map.empty ws
                    else
                        let zs = Data.List.map (\x -> case x of {AAbs (Var z) -> z}) xs in
                        fromList[(y, L 1.0 zs)]
            else
                error ("could not interpret the expression " ++ show aexpr)

-- linf-norm
aexprToExpr y (AMaxs xs) =

            let ys = Data.List.filter (\x -> case x of {AAbs (Var _) -> True; _ -> False}) xs in
            if length ys == length xs then
                        let zs = Data.List.map (\x -> case x of {AAbs (Var x') -> x'}) xs in
                        fromList[(y, LInf zs)]
            else
                let zs = Data.List.map (\x -> y ++ "~" ++ show x) [1..length xs - 1] in
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

