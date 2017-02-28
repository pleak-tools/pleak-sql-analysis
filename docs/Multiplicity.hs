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

  -- Truncated subtraction. May be partial defined.
  mSub :: m -> m -> Maybe m

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

  mSub x Empty = Just x
  mSub _ Singleton = Just Empty

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

  mSub (FiniteM x) (FiniteM y) = Just $ FiniteM $ max 0 (x - y)

  mZero = FiniteM 0
  mOne = FiniteM 1

-- For multisets that may contain infinite duplicates
-- TODO: not a very good name
data OmegaM
  = Finite Int
  | Infinite
  deriving (Eq, Ord)

instance Multiplicity OmegaM where
  mAdd Infinite _ = Infinite
  mAdd _ Infinite = Infinite
  mAdd (Finite m) (Finite n) = Finite (m + n)

  mMul (Finite 0) _ = mZero
  mMul _ (Finite 0) = mZero
  mMul Infinite _ = Infinite
  mMul _ Infinite = Infinite
  mMul (Finite m) (Finite n) = Finite (m + n)

  mSub Infinite Infinite = Nothing
  mSub (Finite _) Infinite = Just mZero
  mSub Infinite (Finite _) = Just Infinite
  mSub (Finite x) (Finite y) = Just $ Finite $ max 0 (x - y)

  mZero = Finite 0
  mOne = Finite 1
