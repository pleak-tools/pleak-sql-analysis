module Multiplicity where

{--------------------------
 - Generic multiplicities -
 --------------------------}

-- Commutative semirings
-- We could use "algebra" library, but it's an overkill
class Ord m => Multiplicity m where
  mAdd :: m -> m -> m
  mMul :: m -> m -> m
  mZero :: m
  mOne :: m

  mFromInteger :: Integer -> m
  mFromInteger 0 = mZero
  mFromInteger 1 = mOne
  mFromInteger n
    | n < 0 = error "Negative multiplicity literal."
    | even n = mTwo `mMul` mFromInteger (n `quot` 2)
    | otherwise = mOne `mAdd` mFromInteger (n - 1)
    where
      mTwo = mOne `mAdd` mOne

{--------------------------------
 - Some concrete multiplicities -
 --------------------------------}

-- For regular sets
data FlatM
  = Empty
  | Singleton
  deriving (Eq, Ord, Show)

instance Multiplicity FlatM where
  mAdd Singleton _ = Singleton
  mAdd _ Singleton = Singleton
  mAdd Empty Empty = Empty

  mMul Empty _ = Empty
  mMul _ Empty = Empty
  mMul Singleton Singleton = Singleton

  mZero = Empty
  mOne = Singleton

-- For multisets
newtype FiniteM = FiniteM Int
  deriving (Eq, Ord)

map2FiniteM :: (Int -> Int -> Int) -> (FiniteM -> FiniteM -> FiniteM)
map2FiniteM f (FiniteM m) (FiniteM n) = FiniteM (f m n)

instance Multiplicity FiniteM where
  mAdd = map2FiniteM (+)
  mMul = map2FiniteM (*)
  mZero = FiniteM 0
  mOne = FiniteM 1

-- For multisets that may contain infinite duplicates
-- TODO: not very good name
data OmegaM
  = Finite Int
  | Infinite
  deriving (Eq, Ord)

instance Multiplicity OmegaM where
  mAdd Infinite _ = Infinite
  mAdd _ Infinite = Infinite
  mAdd (Finite m) (Finite n) = Finite (m + n)

  mMul (Finite 0) _ = Finite 0
  mMul _ (Finite 0) = Finite 0
  mMul Infinite _ = Infinite
  mMul _ Infinite = Infinite
  mMul (Finite m) (Finite n) = Finite (m + n)

  mZero = Finite 0
  mOne = Finite 1
