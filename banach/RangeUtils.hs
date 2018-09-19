module RangeUtils where

import PolicyQ (VarState(..))
import qualified Banach as B (lpnorm, linfnorm)

infinity :: Double
infinity = 1/0

-- upper bound on the absolute value
getGubFromVs :: VarState -> Double
getGubFromVs (Range lb ub) = max (abs lb) ub
getGubFromVs _             = infinity

-- upper bound on the actual value
getUbFromVs :: VarState -> Double
getUbFromVs (Range lb ub) = ub
getUbFromVs _             = infinity

-- lower bound on the actual value
getLbFromVs :: VarState -> Double
getLbFromVs (Range lb ub) = lb
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


