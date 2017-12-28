-- This module computes smooth derivative sensitivity in Banach spaces.
module Banach where

import Text.Printf
import Debug.Trace

type Var = Int                    -- variable corresponding to column i (starting from 0)

-- this simultaneously defines a function E to be analyzed and a norm N on its domain
-- expressions of type Expr use values from a single row
data Expr = Power Var Double      -- x^r with norm | |
          | Exp Double Var        -- e^(r*x) with norm | |
          | ScaleNorm Double Expr -- E with norm a * N
          | ZeroSens Expr         -- E with sensitivity forced to zero (the same as ScaleNorm with a -> infinity)
          | L Double [Var]        -- ||(x1,...,xn)||_p with l_q-norm where q = p/(p-1)
          | LInf [Expr]           -- same with p = infinity, q = 1
          | Prod [Expr]           -- E1*...*En with norm ||(N1,...,Nn)||_1
  deriving Show

-- expressions of type TableExpr use values from the whole table
data TableExpr = Min Expr         -- min (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]

-- SUB g beta0  is a value such that
--   g beta  is a beta-smooth upper bound of a function f at a certain point x for each beta >= beta0
--   beta0  is the minimum (infimum) allowed value of beta (if it is 0 then it is recommended to take beta = defaultBeta)
data SmoothUpperBound = SUB {
  subg :: Double -> Double,
  subBeta :: Double}

instance Show SmoothUpperBound where
  show (SUB g beta0) = let beta = chooseBeta beta0
                       in if beta >= beta0 then printf "%0.3f (beta = %0.3f)" (g beta) beta
                                           else printf "ERROR (beta = %0.3f but must be >= %0.3f)" beta beta0

data AnalysisResult = AR {
  fx :: Double,             -- value of the analyzed function (f(x))
  subf :: SmoothUpperBound, -- smooth upper bound of the absolute value of the analyzed function itself
  sdsf :: SmoothUpperBound} -- smooth upper bound of the derivative sensitivity of the analyzed function
  deriving Show

epsilon :: Double
epsilon = 0.5

gamma :: Double
gamma = 4.0

defaultBeta :: Double
defaultBeta = epsilon / (2 * (gamma + 1))

fixedBeta :: Maybe Double
fixedBeta = Nothing -- determine beta automatically
--fixedBeta = Just 0.7 -- use fixed value of beta

chooseBeta :: Double -> Double
chooseBeta beta0 = case fixedBeta of Just beta -> beta
                                     Nothing -> if beta0 == 0 then defaultBeta
                                                              else beta0

type Row = [Double]
type Table = [Row]

-- the database table on which the query is executed
table :: Table
table = [
  [2.0],
  [1.0],
  [3.0]]

exampleRow :: Row
exampleRow = [3,4,5]

-- a sample query
example :: Expr
example = Prod [ScaleNorm 0.1 $ L 2 [0,1], Exp (-log 2) 2] -- full sensitivity, i.e. sensitivity w.r.t. component [0,1,2]
exampleComp01 = Prod [ScaleNorm 0.1 $ L 2 [0,1], ZeroSens $ Exp (-log 2) 2] -- sensitivity w.r.t. component [0,1]
exampleComp2 = Prod [ZeroSens $ ScaleNorm 0.1 $ L 2 [0,1], Exp (-log 2) 2] -- sensitivity w.r.t. component [2]

-- compute ||(x_1,...,x_n)||_p
lpnorm :: Double -> [Double] -> Double
lpnorm p xs = (sum $ map (**p) xs) ** (1/p)

-- compute ||(x_1,...,x_n)||_infinity
linfnorm :: [Double] -> Double
linfnorm = maximum

-- return xs with the element (xs !! i) removed
skipith :: Int -> [a] -> [a]
skipith i xs = let (ys,_:zs) = splitAt i xs in ys ++ zs

analyzeExpr :: Row -> Expr -> AnalysisResult
analyzeExpr row expr = trace ("analyzeExpr: " ++ show expr ++ " -> " ++ show res) res where
 res =
  case expr of
    Exp r i ->
      let x = row !! i
      in AR {fx = exp (r * x),
             subf = SUB (const $ exp (r * x)) (abs r),
             sdsf = SUB (const $ abs r * exp (r * x)) (abs r)}
    ScaleNorm a e1 ->
      let AR fx1 (SUB subf1g subf1beta) (SUB sdsf1g sdsf1beta) = analyzeExpr row e1
      in AR {fx = fx1,
             subf = SUB (\ beta -> subf1g (beta*a)) (subf1beta/a),
             sdsf = SUB (\ beta -> sdsf1g (beta*a) / a) (sdsf1beta/a)}
    ZeroSens e1 ->
      let AR fx1 (SUB subf1g subf1beta) (SUB sdsf1g sdsf1beta) = analyzeExpr row e1
      in AR {fx = fx1,
             subf = SUB (const fx1) 0,
             sdsf = SUB (const 0) 0}
    L p is ->
      let xs = map (row !!) is
          y = lpnorm p xs
      in AR {fx = y,
             subf = SUB (\ beta -> if y >= 1/beta then y else exp (beta * y - 1) / beta) 0,
             sdsf = SUB (const 1) 0}
    Prod es ->
      let ars = map (analyzeExpr row) es
          fxs = map fx ars
          subfs = map subf ars
          sdsfs = map sdsf ars
          subfBetas = map subBeta subfs
          sdsfBetas = map subBeta sdsfs
          subgs = map subg subfs
          sdsgs = map subg sdsfs
          n = length es
          c i beta = ((sdsgs !! i) beta) * product (map ($ beta) $ skipith i subgs)
      in AR {fx = product fxs,
             subf = SUB (\ beta -> product (map ($ beta) subgs)) (maximum subfBetas),
             sdsf = SUB (\ beta -> linfnorm (map (\ i -> c i beta) [0..n-1])) (maximum (subfBetas ++ sdsfBetas))}
