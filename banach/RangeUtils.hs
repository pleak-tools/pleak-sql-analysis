module RangeUtils where

import VarstateQ (VarState(..), VState(..), getUb)
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
-- polymorphic ranges


-- upper bound on the absolute value
getGubFromVsPoly :: (a -> a -> a) -> (a -> a) -> a -> VState a -> a
getGubFromVsPoly fmax fabs inf (Range lb ub) = fmax (fabs lb) ub
getGubFromVsPoly _ _ inf _                   = inf

-- upper bound on the actual value
getUbFromVsPoly :: a -> VState a -> a
getUbFromVsPoly inf (Range lb ub) = ub
getUbFromVsPoly inf _             = inf

-- lower bound on the actual value
getLbFromVsPoly :: a -> VState a -> a
getLbFromVsPoly ninf (Range lb ub) = lb
getLbFromVsPoly ninf _             = ninf

getRangeFromVsPoly :: a -> a -> VState a -> VState a
getRangeFromVsPoly inf ninf vs = Range (getLbFromVsPoly ninf vs) (getUbFromVsPoly inf vs)

rangeMulPoly :: (a -> a -> a) -> ([a] -> a) -> ([a] -> a) -> VState a -> VState a -> VState a
rangeMulPoly fmul fmins fmaxs (Range x1 x2) (Range y1 y2) = Range (fmins xys) (fmaxs xys)
  where
    xys = [fmul x1 y1, fmul x1 y2, fmul x2 y1, fmul x2 y2]

rangeProductPoly :: (a -> a -> a) -> ([a] -> a) -> ([a] -> a) -> [VState a] -> VState a
rangeProductPoly fmul fmins fmaxs = foldl1 (rangeMulPoly fmul fmins fmaxs)

rangeAbsPoly :: a -> (a -> a) -> (a -> a -> a) -> (a -> a -> a) -> (a -> a -> a) -> (a -> a -> a) -> (a -> a -> a -> a) -> VState a -> VState a
rangeAbsPoly zero fabs fle fand fmin fmax fif (Range x y) = Range lb ub
  where
    ub = fmax (fabs x) (fabs y)
    lb = fif (fand (fle zero x) (fle y zero)) zero (fmin (fabs x) (fabs y))

rangeLpNormPoly :: Double -> a -> a -> a -> (a -> a) -> (a -> a -> a) -> (a -> a -> a) -> (a -> a -> a) -> (a -> a -> a) -> (a -> a -> a -> a) -> (Double -> [a] -> a)
                   -> [VState a] ->  VState a
rangeLpNormPoly p inf ninf zero fabs fle fand fmin fmax fif flpnorm rs0 =
  let rs = map (rangeAbsPoly zero fabs fle fand fmin fmax fif) rs0
      ubs = map (getUbFromVsPoly inf) rs
      lbs = map (getLbFromVsPoly ninf) rs
      ub = flpnorm p ubs
      lb = flpnorm p lbs
  in Range lb ub

rangeLInfNormPoly :: a -> a -> a -> (a -> a) -> (a -> a -> a) -> (a -> a -> a) -> (a -> a -> a) -> (a -> a -> a) -> (a -> a -> a -> a) -> ([a] -> a)
                   -> [VState a] ->  VState a
rangeLInfNormPoly inf ninf zero fabs fle fand fmin fmax fif flinfnorm rs0 =
  let rs = map (rangeAbsPoly zero fabs fle fand fmin fmax fif) rs0
      ubs = map (getUbFromVsPoly inf) rs
      lbs = map (getLbFromVsPoly ninf) rs
      ub = flinfnorm ubs
      lb = flinfnorm lbs
  in Range lb ub

rangeDivPoly :: (a -> a -> a) -> ([a] -> a) -> ([a] -> a) -> VState a -> VState a -> VState a
rangeDivPoly fdiv fmins fmaxs (Range x1 x2) (Range y1 y2) = Range (fmins xys) (fmaxs xys)
  where
    xys = [fdiv x1 y1, fdiv x1 y2, fdiv x2 y1, fdiv x2 y2]

rangeAddPoly :: (a -> a -> a) -> VState a -> VState a -> VState a
rangeAddPoly fadd (Range x1 x2) (Range y1 y2) = Range (fadd x1 y1) (fadd x2 y2)

rangeSumPoly :: (a -> a -> a) -> [VState a] -> VState a
rangeSumPoly fadd = foldl1 (rangeAddPoly fadd)

rangeNegPoly :: (a -> a) ->VState a -> VState a
rangeNegPoly fneg (Range x1 x2) = Range (fneg x2) (fneg x1)

rangeSubPoly :: (a -> a -> a) -> (a -> a) -> VState a -> VState a -> VState a
rangeSubPoly fadd fneg x1 x2 = rangeAddPoly fadd x1 (rangeNegPoly fneg x2)

rangeNotPoly :: (a -> a) -> VState a -> VState a
rangeNotPoly fnot (Range x1 x2) = Range (fnot x2) (fnot x1)

rangeMinPoly :: (a -> a -> a) -> VState a -> VState a -> VState a
rangeMinPoly fmin (Range x1 x2) (Range y1 y2) = Range (fmin x1 y1) (fmin x2 y2)

rangeMinsPoly :: (a -> a -> a) -> [VState a] -> VState a
rangeMinsPoly fmin = foldl1 (rangeMinPoly fmin)

rangeAndPoly  = rangeMinPoly
rangeAndsPoly = rangeMinsPoly

rangeMaxPoly :: (a -> a -> a) -> VState a -> VState a -> VState a
rangeMaxPoly fmax (Range x1 x2) (Range y1 y2) = Range (fmax x1 y1) (fmax x2 y2)

rangeMaxsPoly :: (a -> a -> a) -> [VState a] -> VState a
rangeMaxsPoly fmax = foldl1 (rangeMinPoly fmax)

rangeOrPoly  = rangeMinPoly
rangeOrsPoly = rangeMinsPoly

rangeXorPoly :: (a -> a -> a) -> (a -> a -> a) -> (a -> a -> a) -> VState a -> VState a -> VState a
rangeXorPoly fxor fmin fmax (Range x1 x2) (Range y1 y2) =
    let z1 = fxor x1 y1 in
    let z2 = fxor x2 y2 in
    Range (fmin z1 z2) (fmax z1 z2)

rangeXorsPoly :: (a -> a -> a) -> (a -> a -> a) -> (a -> a -> a) -> [VState a] -> VState a
rangeXorsPoly fxor fmin fmax = foldl1 (rangeXorPoly fxor fmin fmax)

rangeMonotonePoly :: (a -> a) -> VState a -> VState a
rangeMonotonePoly f (Range x1 x2) = Range (f x1) (f x2) 

rangeLTPoly :: (a -> a -> a) -> VState a -> VState a -> VState a
rangeLTPoly flt (Range x1 x2) (Range y1 y2) = Range (flt x2 y1) (flt x1 y2)

rangeLEPoly :: (a -> a -> a) -> VState a -> VState a -> VState a
rangeLEPoly fle (Range x1 x2) (Range y1 y2) = Range (fle x2 y1) (fle x1 y2)


