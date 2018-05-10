module AexprQ where

import Data.List
import qualified Data.Map as M
import qualified Data.Set as S

import ErrorMsg
import ExprQ

-- the default alpha value for Tauoids and Sigmoids
a = 0.1

-- we want to parse complex expressions and transform them to Expr afterwards
data AExpr a
  = AVar a
  | AConst Double
  | AText String
--  | ASubExpr Expr
  | AUnary  AUnOp (AExpr a)
  | ABinary ABinOp (AExpr a) (AExpr a)
  | AAbs  (AExpr a)
  | ASum  [AExpr a]
  | AProd [AExpr a]
  | AMins [AExpr a]
  | AMaxs [AExpr a]
  | AAnds [AExpr a]
  | AOrs  [AExpr a]
  | AXors [AExpr a] -- we assume that it is applied only to mutually exclusive conditions
  deriving (Show)

data AUnOp
  = AAbsBegin | AAbsEnd 
  | ALn
  | ANeg | ANot
  | AExp   Double
  | APower Double
  deriving (Show)

data ABinOp
  = ADiv | AMult | AAdd | ASub
  | AMin | AMax 
  | AAnd | AOr | AXor
  | ALT | AEQ | AGT | ALike
  deriving (Show)

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
            let f = (\v -> AUnary (APower (-1.0)) (AUnary ALn v)) in
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
aexprNormalize x = x

---------------------------------------------------------------------------------------------------------
-- we do not convert to aggregation since it comes separately
-- we do not convert to scaleNorm and zeroSens since they come from the database norm
aexprToExpr :: VarName -> AExpr VarName -> (M.Map VarName Expr)

-- TODO this is temporary, can be improved
aexprToExpr y (AVar "min~") = M.fromList [(y,ARMin)]
aexprToExpr y (AVar "max~") = M.fromList [(y,ARMax)]

--
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

aexprToExpr y (AUnary ALn  (AConst c)) = M.fromList [(y, Const (log c))]
aexprToExpr y (AConst c)   = M.fromList [(y, Const c)]
aexprToExpr y (AVar x)     = M.fromList [(y, Id x)]
--aexprToExpr y (ASubExpr e) = M.fromList [(y, e)]

aexprToExpr y (ABinary ALike x1 x2) =
    let z1     = y ++ "~1" in
    let z2     = y ++ "~2" in
    M.union (aexprToExpr z1 x1) $ M.union (aexprToExpr z2 x2) $ M.fromList [(y, Like z1 z2)]

aexprToExpr y (ABinary ALT x (AConst c)) = 
    let z      = y ++ "~0" in
    let w1     = y ++ "~1" in
    let w2     = y ++ "~2" in
    M.union (aexprToExpr z x) $ M.fromList [(y, Sum ["1",w2]), (w2, Prod ["-1",w1]), (w1, Sigmoid a c z), ("1", Const (1.0)), ("-1", Const (-1.0))]

aexprToExpr y (ABinary ALT x1 x2) = 
    let z       = y ++ "~0" in 
    let z1      = y ++ "~1" in
    let z2      = y ++ "~2" in
    let w       = y ++ "~3" in
    M.union (aexprToExpr z1 x1) $ M.union (aexprToExpr z2 x2) $ M.fromList [(y, Comp GT z1 z2)]

aexprToExpr y (ABinary AEQ x (AConst c)) = 
    let z      = y ++ "~0" in
    M.union (aexprToExpr z x) $ M.fromList [(y, Tauoid  a c z)]

aexprToExpr y (ABinary AEQ x1 x2) = 
    let z      = y ++ "~0" in 
    let z1     = y ++ "~1" in
    let z2     = y ++ "~2" in
    M.union (aexprToExpr z1 x1) $ M.union (aexprToExpr z2 x2) $ M.fromList [(y, Comp EQ z1 z2)]

aexprToExpr y (ABinary AGT x (AConst c)) = 
    let z      = y ++ "~0" in
    let z1     = y ++ "~1" in
    M.union (aexprToExpr z x) $ M.fromList [(y, Sigmoid a c z)]

aexprToExpr y (ABinary AGT x1 x2) = 
    let z      = y ++ "~0" in 
    let z1     = y ++ "~1" in
    let z2     = y ++ "~2" in
    let w      = y ++ "~3" in
    M.union (aexprToExpr z1 x1) $ M.union (aexprToExpr z2 x2) $ M.fromList [(y, Comp GT z2 z1)]

-- lp-norm
aexprToExpr y aexpr@(AUnary (APower pinv) (ASum xs)) =

    let p = 1 / pinv in

    -- if p is an even number, we do not need to take absolute value of the arguments
    let pint = round p in
    let isEven = (mod pint 2 == 0) && (p == fromIntegral pint) in

    -- collect all expression and variable arguments separately
    let ysExpr = filter (\x -> case x of {AUnary (APower q) (AAbs _)        -> p == q; AUnary (APower q) _        -> p == q && isEven; _ -> False}) xs in
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

aexprToExpr y (AUnary (APower c) (AVar x))              = M.fromList [(y, Power x c)]
aexprToExpr y (AUnary (APower c) (AUnary ALn (AVar x))) = M.fromList [(y, PowerLN x c)]
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

aexprToExpr y (AAnds xs) = aexprToExpr y $ AProd xs
aexprToExpr y (AOrs  xs) = aexprToExpr y $ AUnary ANot (AProd (map (AUnary ANot) xs))
aexprToExpr y (AXors xs) = aexprToExpr y $ ASum xs


-- we may possibly add more interesting expressions that can be reduced to Expr
aexprToExpr y aexpr = error $ error_queryExpr aexpr
------------------------------------------------------------------------------------
aexprToString :: AExpr String -> String
aexprToString aexpr =
    case aexpr of
        AVar x -> x
        AConst c -> show c
        AText c -> "\'" ++ c ++ "\'"

        AAbs x -> "abs(" ++ aexprToString x ++ ")"
        ASum xs -> "(" ++ intercalate " + " (map aexprToString xs) ++ ")"
        AProd xs -> "(" ++ intercalate " * " (map aexprToString xs) ++ ")"
        AMins xs -> "least(" ++ intercalate "," (map aexprToString xs) ++ ")"
        AMaxs xs -> "greatest(" ++ intercalate "," (map aexprToString xs) ++ ")"
        AAnds xs -> "(" ++ intercalate " AND " (map aexprToString xs) ++ ")"
        AOrs  xs -> "(" ++ intercalate " OR " (map aexprToString xs) ++ ")"
        AXors xs -> "(" ++ intercalate " OR " (map aexprToString xs) ++ ")"

        AUnary ALn x -> "log(" ++ aexprToString x ++ ")"
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
        ABinary AEQ  x1 x2 -> "(" ++ aexprToString x1 ++ " = " ++ aexprToString x2 ++ ")"
        ABinary AGT x1 x2  -> "(" ++ aexprToString x1 ++ " > " ++ aexprToString x2 ++ ")"
        ABinary ALike x1 x2 -> "(" ++ aexprToString x1 ++ " LIKE " ++ aexprToString x2 ++ ")"

------------------------------------------------------------------------------------
updatePreficesAexpr :: (S.Set String) -> VarName -> AExpr VarName -> AExpr VarName
updatePreficesAexpr fullTablePaths prefix aexpr =
    case aexpr of
        AVar x -> AVar $ processBase x
        AConst c -> AConst c
        AText c -> AText c

        AAbs x -> AAbs $ processRec x
        ASum xs -> ASum (map processRec xs)
        AProd xs -> AProd (map processRec xs)
        AMins xs -> AMins (map processRec xs)
        AMaxs xs -> AMaxs (map processRec xs)
        AAnds xs -> AAnds (map processRec xs)
        AOrs  xs -> AOrs (map processRec xs)
        AXors xs -> AXors (map processRec xs)

        AUnary ALn x -> AUnary ALn $ processRec x
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
        ABinary AEQ  x1 x2 -> ABinary AEQ (processRec x1) (processRec x2)
        ABinary AGT x1 x2  -> ABinary AGT (processRec x1) (processRec x2)
        ABinary ALike x1 x2 -> ABinary ALike (processRec x1) (processRec x2)

   where processRec  x = updatePreficesAexpr fullTablePaths prefix x
         processBase x = updatePrefices      fullTablePaths prefix x

--------------------------
-- get all variables
getAllAExprVars :: (Ord a, Show a) => AExpr a -> S.Set a
getAllAExprVars aexpr =
    case aexpr of
        AVar x -> processBase x
        AConst c -> S.empty
        AText c -> S.empty

        AAbs x  -> processRec x
        ASum  xs -> foldr S.union S.empty $ map processRec xs
        AProd xs -> foldr S.union S.empty $ map processRec xs
        AMins xs -> foldr S.union S.empty $ map processRec xs
        AMaxs xs -> foldr S.union S.empty $ map processRec xs
        AAnds xs -> foldr S.union S.empty $ map processRec xs
        AOrs  xs -> foldr S.union S.empty $ map processRec xs
        AXors xs -> foldr S.union S.empty $ map processRec xs

        AUnary ALn x -> processRec x
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
        ABinary AEQ  x1 x2 -> S.union (processRec x1) (processRec x2)
        ABinary AGT x1 x2  -> S.union (processRec x1) (processRec x2)
        ABinary ALike x1 x2 -> S.union (processRec x1) (processRec x2)
    where processRec x = getAllAExprVars x
          processBase x = S.singleton x

aexprToColSet :: (Show a, Ord a, Show b, Ord b) => M.Map a b -> AExpr a -> S.Set b
aexprToColSet inputMap aexpr = S.map (inputMap ! ) $ getAllAExprVars aexpr

--------------------------
-- substitute variable subexpressions
aexprSubstitute :: (Ord a, Show a) => (M.Map a (AExpr a)) -> AExpr a -> AExpr a
aexprSubstitute aexprMap aexpr =
    case aexpr of
        AVar x -> processBase x
        AConst c -> AConst c
        AText c -> AText c

        AAbs x -> AAbs $ processRec x
        ASum xs -> ASum (map processRec xs)
        AProd xs -> AProd (map processRec xs)
        AMins xs -> AMins (map processRec xs)
        AMaxs xs -> AMaxs (map processRec xs)
        AAnds xs -> AAnds (map processRec xs)
        AOrs  xs -> AOrs (map processRec xs)
        AXors xs -> AXors (map processRec xs)

        AUnary ALn x -> AUnary ALn $ processRec x
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
        ABinary AEQ  x1 x2 -> ABinary AEQ (processRec x1) (processRec x2)
        ABinary AGT x1 x2  -> ABinary AGT (processRec x1) (processRec x2)
        ABinary ALike x1 x2 -> ABinary ALike (processRec x1) (processRec x2)
    where processRec x = aexprSubstitute aexprMap x
          processBase x = if M.member x aexprMap then aexprMap ! x else AVar x

