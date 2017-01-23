import Control.Arrow (second)

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

{-----------------------------
 - Generic multisets or bags -
 -----------------------------}

-- Very simple multiset representation.
-- Has following constraints:
-- 1. does not contain any elements with 0 multiplicity
-- 2. sorted by first component
-- 3. first components are unique
-- 4. finite length
type Bag m a = [(a, m)]

bagIntersect :: (Ord m, Ord a) => Bag m a -> Bag m a -> Bag m a
bagIntersect _ [] = []
bagIntersect [] _ = []
bagIntersect (a : as) (b : bs) =
  case compare (fst a) (fst b) of
    LT -> bagIntersect as (b : bs)
    EQ -> (fst a, min (snd a) (snd b)) : bagIntersect as bs
    GT -> bagIntersect (a : as) bs

bagUnion :: (Multiplicity m, Ord a) => Bag m a -> Bag m a -> Bag m a
bagUnion as [] = as
bagUnion [] bs = bs
bagUnion (a : as) (b : bs) =
  case compare (fst a) (fst b) of
    LT -> a : bagUnion as (b : bs)
    GT -> b : bagUnion (a : as) bs
    EQ -> (fst a, snd a `mAdd` snd b) : bagUnion as bs

bagCross :: Multiplicity m => Bag m a -> Bag m b -> Bag m (a, b)
bagCross as bs = [((a,b), n `mMul` m) | (a, n) <- as, (b, m) <- bs]

bagSubset :: (Ord m, Ord a) => Bag m a -> Bag m a -> Bool
bagSubset [] _ = True
bagSubset _ [] = False
bagSubset (a : as) (b : bs) =
  case compare (fst a) (fst b) of
    LT -> False
    GT -> bagSubset (a : as) bs
    EQ -> snd a <= snd b && bagSubset as bs

bagElem :: (Multiplicity m, Ord a) => a -> Bag m a -> Bool
bagElem x = bagSubset [(x, mOne)]

bagSquash :: Multiplicity n => Bag m a -> Bag n a
bagSquash = map (second (const mOne))
