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
          | L Double [Var]        -- ||(x1,...,xn)||_p with l_p-norm
          | LInf [Var]            -- same with p = infinity
          | Prod [Expr]           -- E1*...*En with norm ||(N1,...,Nn)||_1
          | Min [Expr]            -- min{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
          | Max [Expr]            -- max{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
  deriving Show

-- expressions of type TableExpr use values from the whole table
data TableExpr = SelectProd Expr        -- product (map E rows) with norm ||(N1,...,Nn)||_1 where Ni is N applied to ith row
               | SelectMin Expr         -- min (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]
               | SelectMax Expr         -- max (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]

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
  [2,3,4],
  [5,6,3],
  [1,3,2],
  [3,4,5]]

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
analyzeExpr row expr = trace ("analyzeExpr " ++ show row ++ ": " ++ show expr ++ " -> " ++ show res) res where
 res =
  case expr of
    Power i r ->
      let x = row !! i
      in if r >= 1 && x > 0
           then AR {fx = x ** r,
                    subf = SUB (\ beta -> if x >= r/beta then x ** r else exp (beta*x - r) * (r/beta)**r) 0,
                    sdsf = SUB (\ beta -> if x >= (r-1)/beta then r * x**(r-1) else r * exp (beta*x - (r-1)) * ((r-1)/beta)**(r-1)) 0}
           else error "analyzeExpr/Power: condition (r >= 1 && x > 0) not satisfied"
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
    LInf is ->
      let xs = map (row !!) is
          y = linfnorm xs
      in AR {fx = y,
             subf = SUB (\ beta -> if y >= 1/beta then y else exp (beta * y - 1) / beta) 0,
             sdsf = SUB (const 1) 0}
    Prod es -> combineArsProd $ map (analyzeExpr row) es
    Min es -> combineArsMin $ map (analyzeExpr row) es
    Max es -> combineArsMax $ map (analyzeExpr row) es

combineArsProd :: [AnalysisResult] -> AnalysisResult
combineArsProd ars =
  let fxs = map fx ars
      subfs = map subf ars
      sdsfs = map sdsf ars
      subfBetas = map subBeta subfs
      sdsfBetas = map subBeta sdsfs
      subgs = map subg subfs
      sdsgs = map subg sdsfs
      n = length ars
      c i beta = ((sdsgs !! i) beta) * product (map ($ beta) $ skipith i subgs)
  in AR {fx = product fxs,
         subf = SUB (\ beta -> product (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> linfnorm (map (\ i -> c i beta) [0..n-1])) (maximum (subfBetas ++ sdsfBetas))}

combineArsMin :: [AnalysisResult] -> AnalysisResult
combineArsMin ars =
  let fxs = map fx ars
      subfs = map subf ars
      sdsfs = map sdsf ars
      subfBetas = map subBeta subfs
      sdsfBetas = map subBeta sdsfs
      subgs = map subg subfs
      sdsgs = map subg sdsfs
  in AR {fx = minimum fxs,
         subf = SUB (\ beta -> minimum (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> maximum (map ($ beta) sdsgs)) (maximum sdsfBetas)}

combineArsMax :: [AnalysisResult] -> AnalysisResult
combineArsMax ars =
  let fxs = map fx ars
      subfs = map subf ars
      sdsfs = map sdsf ars
      subfBetas = map subBeta subfs
      sdsfBetas = map subBeta sdsfs
      subgs = map subg subfs
      sdsgs = map subg sdsfs
  in AR {fx = maximum fxs,
         subf = SUB (\ beta -> maximum (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> maximum (map ($ beta) sdsgs)) (maximum sdsfBetas)}

analyzeTableExpr :: Table -> TableExpr -> AnalysisResult
analyzeTableExpr rows te =
  case te of
    SelectMin expr -> combineArsMin $ map (`analyzeExpr` expr) rows
    SelectMax expr -> combineArsMax $ map (`analyzeExpr` expr) rows
    SelectProd expr -> combineArsProd $ map (`analyzeExpr` expr) rows
