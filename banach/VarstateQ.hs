module VarstateQ where

import qualified Data.Map as M
import ErrorMsg

---------------------------------------------------
---- variable state and policy data structures ----
---------------------------------------------------

data VState a
  = Exact | None
  | Approx a                       | ApproxWrtLp Double a           | ApproxWrtLinf a
  | IntSubSet   [Int]              | SubSet   [String]              | Range   a a                | Total Int
  | IntSubSetUn [Int]              | SubSetUn [String]              | RangeUn a a                | TotalUn Int
  | IntSubSetPr (M.Map Int Double) | SubSetPr (M.Map String Double) | RangePr a (M.Map a Double)
  | Normal a a
  deriving (Show)


type VarState = VState Double

getUb :: Double -> M.Map Double Double -> Double
getUb lb mp = foldr max lb (M.keys mp)
