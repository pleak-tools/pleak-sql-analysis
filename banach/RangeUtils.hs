module RangeUtils where

import PolicyQ (VarState(..), VState(..), getUb)
import AexprQ
import qualified Banach as B (lpnorm, linfnorm)

infinity :: Double
infinity = 1/0

-- we should extend everything also to RangeUn and RangePr,
-- just convert them to a Range
anyVarStateToRange (RangeUn lb ub) = Range lb ub
anyVarStateToRange (RangePr lb mp) = Range lb (getUb lb mp)
anyVarStateToRange x               = x

-- upper bound on the absolute value
getGubFromVs :: VarState -> Double
getGubFromVs (Range   lb ub) = max (abs lb) ub
getGubFromVs _             = infinity

-- upper bound on the actual value
getUbFromVs :: VarState -> Double
getUbFromVs (Range   lb ub) = ub
getUbFromVs _             = infinity

-- lower bound on the actual value
getLbFromVs :: VarState -> Double
getLbFromVs (Range   lb ub) = lb
getLbFromVs _             = -infinity

getRangeFromVs :: VarState -> VarState
getRangeFromVs vs = Range (getLbFromVs vs) (getUbFromVs vs)

rangeMul :: VarState -> VarState -> VarState
rangeMul (Range x1 x2) (Range y1 y2) = Range (minimum xys) (maximum xys)
  where
    xys = [x1*y1, x1*y2, x2*y1, x2*y2]

rangeProduct :: [VarState] -> VarState
rangeProduct = foldl1 rangeMul

rangeAbs :: VarState -> VarState
rangeAbs (Range x y) = Range lb ub
  where
    ub = max (abs x) (abs y)
    lb = if x <= 0 && y >= 0 then 0 else min (abs x) (abs y)

rangeLpNorm :: Double -> [VarState] -> VarState
rangeLpNorm p rs0 =
  let rs = map rangeAbs rs0
      ubs = map getUbFromVs rs
      lbs = map getLbFromVs rs
      ub = B.lpnorm p ubs
      lb = B.lpnorm p lbs
  in Range lb ub

rangeLInfNorm :: [VarState] -> VarState
rangeLInfNorm rs0 =
  let rs = map rangeAbs rs0
      ubs = map getUbFromVs rs
      lbs = map getLbFromVs rs
      ub = B.linfnorm ubs
      lb = B.linfnorm lbs
  in Range lb ub

--------------------------------------------------------------------------------------------
-- TODO it would be nicer to use some general class, but I do not know how to do it nicely
-- TODO we do not use it anywhere yet

infinityA :: AExpr a
infinityA = AConst (1/0)

-- upper bound on the absolute value
getGubFromVsA :: VState (AExpr a) -> AExpr a
getGubFromVsA (Range lb ub) = ABinary AMax (AAbs lb) ub
getGubFromVsA _             = infinityA

-- upper bound on the actual value
getUbFromVsA :: VState (AExpr a) -> AExpr a
getUbFromVsA (Range lb ub) = ub
getUbFromVsA _             = infinityA

-- lower bound on the actual value
getLbFromVsA :: VState (AExpr a) -> AExpr a
getLbFromVsA (Range lb ub) = lb
getLbFromVsA _             = AUnary ANeg infinityA

getRangeFromVsA :: VState (AExpr a) -> VState (AExpr a)
getRangeFromVsA vs = Range (getLbFromVsA vs) (getUbFromVsA vs)

rangeMulA :: VState (AExpr a) -> VState (AExpr a) -> VState (AExpr a)
rangeMulA (Range x1 x2) (Range y1 y2) = Range (AMins xys) (AMaxs xys)
  where
    xys = [ABinary AMult x1 y1, ABinary AMult x1 y2, ABinary AMult x2 y1, ABinary AMult x2 y2]

rangeProductA :: [VState (AExpr a)] -> VState (AExpr a)
rangeProductA = foldl1 rangeMulA

rangeAbsA :: VState (AExpr a) -> VState (AExpr a)
rangeAbsA (Range x y) = Range lb ub
  where
    ub = ABinary AMax (AAbs x) (AAbs y)
    lb = ABinary AMult (ABinary ASub (AConst 1) (ABinary AMult (ABinary ALE x (AConst 0)) (ABinary AGE y (AConst 0)))) (ABinary AMin (AAbs x) (AAbs y))
{-
rangeLpNormA :: Double -> [ VState (AExpr a)] ->  VState (AExpr a)
rangeLpNormA p rs0 =
  let rs = map rangeAbsA rs0
      ubs = map getUbFromVsA rs
      lbs = map getLbFromVsA rs
      ub = aexprLpnorm p ubs
      lb = aexprLpnorm p lbs
  in Range lb ub

rangeLInfNormA :: [VarState] -> VarState
rangeLInfNormA rs0 =
  let rs = map rangeAbsA rs0
      ubs = map getUbFromVsA rs
      lbs = map getLbFromVsA rs
      ub = aexprLinfnorm ubs
      lb = aexprLinfnorm lbs
  in Range lb ub
-}
rangeMinA :: VState (AExpr a) -> VState (AExpr a) -> VState (AExpr a)
rangeMinA (Range x1 x2) (Range y1 y2) = Range (ABinary AMin x1 y1) (ABinary AMin x2 y2)

rangeMinsA :: [VState (AExpr a)] -> VState (AExpr a)
rangeMinsA = foldl1 rangeMinA

rangeMaxA :: VState (AExpr a) -> VState (AExpr a) -> VState (AExpr a)
rangeMaxA (Range x1 x2) (Range y1 y2) = Range (ABinary AMax x1 y1) (ABinary AMax x2 y2)

rangeMaxsA :: [VState (AExpr a)] -> VState (AExpr a)
rangeMaxsA = foldl1 rangeMaxA

