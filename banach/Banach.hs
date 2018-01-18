-- This module computes smooth derivative sensitivity in Banach spaces.
module Banach where

import ProgramOptions

import Text.Printf
import Debug.Trace

type Var = Int                    -- variable corresponding to column i (starting from 0)

-- this simultaneously defines a function E to be analyzed and a norm N on its domain
-- expressions of type Expr use values from a single row
data Expr = Power Var Double         -- x^r with norm | |
          | PowerLN Var Double       -- x^r with logarithmic norm: ||x|| = |ln x|, addition in Banach space is multiplication of real numbers
          | ComposePower Expr Double -- E^r with norm N
          | Exp Double Var           -- e^(r*x) with norm | |
          | ScaleNorm Double Expr    -- E with norm a * N
          | ZeroSens Expr            -- E with sensitivity forced to zero (the same as ScaleNorm with a -> infinity)
          | L Double [Var]           -- ||(x1,...,xn)||_p with l_p-norm
          | ComposeL Double [Expr]   -- ||(E1,...,En)||_p with norm ||(N1,...,Nn)||_p
          | LInf [Var]               -- same with p = infinity
          | Prod [Expr]              -- E1*...*En with norm ||(N1,...,Nn)||_1
          | Min [Expr]               -- min{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
          | Max [Expr]               -- max{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
  deriving Show

-- expressions of type TableExpr use values from the whole table
data TableExpr = SelectProd Expr        -- product (map E rows) with norm ||(N1,...,Nn)||_1 where Ni is N applied to ith row
               | SelectMin Expr         -- min (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]
               | SelectMax Expr         -- max (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]
               | SelectL Double Expr    -- ||(E1,...,En)||_p with norm ||(N1,...,Nn)||_p
  deriving Show

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
epsilon = 1.0

gamma :: Double
gamma = 4.0

defaultBeta :: Double
defaultBeta = epsilon / (2 * (gamma + 1))

fixedBeta :: Maybe Double
fixedBeta = Nothing -- determine beta automatically
--fixedBeta = Just 0.05 -- use fixed value of beta

chooseBeta :: Double -> Double
chooseBeta beta0 = case fixedBeta of Just beta -> beta
                                     Nothing -> if beta0 == 0 then defaultBeta
                                                              else beta0

-- with custom defaultBeta and fixedBeta
chooseBetaCustom :: Double -> Maybe Double -> Double -> Double
chooseBetaCustom defaultBeta fixedBeta beta0 = case fixedBeta of Just beta -> beta
                                                                 Nothing -> if beta0 == 0 then defaultBeta
                                                                                          else beta0

chooseSUBBeta :: Double -> Maybe Double -> SmoothUpperBound -> Double
chooseSUBBeta defaultBeta fixedBeta (SUB g beta0) =
                              let beta = chooseBetaCustom defaultBeta fixedBeta beta0
                              in if beta >= beta0 then beta
                                                  else error $ printf "ERROR (beta = %0.3f but must be >= %0.3f)" beta beta0

type Row = [Double]
type Table = [Row]

-- the database table on which the query is executed
table :: Table
table = [
  [2,3,4],
  [5,6,3],
  [1,3,2],
  [3,4,5]]

table2 :: Table
table2 = [
  [3,4,20],
  [6,8,30]]

exampleRow :: Row
exampleRow = [3,4,5]

-- a sample query
example :: Expr
example = Prod [ScaleNorm 0.1 $ L 2 [0,1], Exp (-log 2) 2] -- full sensitivity, i.e. sensitivity w.r.t. component [0,1,2]
exampleComp01 = Prod [ScaleNorm 0.1 $ L 2 [0,1], ZeroSens $ Exp (-log 2) 2] -- sensitivity w.r.t. component [0,1]
exampleComp2 = Prod [ZeroSens $ ScaleNorm 0.1 $ L 2 [0,1], Exp (-log 2) 2] -- sensitivity w.r.t. component [2]

example2 :: TableExpr
example2 = SelectMin $ Prod [L 2 [0,1], ScaleNorm 20 $ PowerLN 2 (-1)]

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
analyzeExpr row expr = {-trace ("analyzeExpr " ++ show row ++ ": " ++ show expr ++ " -> " ++ show res)-} res where
 res =
  case expr of
    Power i r ->
      let x = row !! i
      in if r >= 1 && x > 0
           then AR {fx = x ** r,
                    subf = SUB (\ beta -> if x >= r/beta then x ** r else exp (beta*x - r) * (r/beta)**r) 0,
                    sdsf = SUB (\ beta -> if x >= (r-1)/beta then r * x**(r-1) else r * exp (beta*x - (r-1)) * ((r-1)/beta)**(r-1)) 0}
           else error "analyzeExpr/Power: condition (r >= 1 && x > 0) not satisfied"
    ComposePower e1 r ->
      let AR gx (SUB subf1g beta1) (SUB sdsf1g beta2) = analyzeExpr row e1
          beta3 = (r-1)*beta1 + beta2
          b1 = if beta3 > 0 then beta1 / beta3 else 1/r
          b2 = if beta3 > 0 then beta2 / beta3 else 1/r
      in if r >= 1 && gx > 0
           then AR {fx = gx ** r,
                    subf = SUB (\ beta -> subf1g (beta / r)) (r*beta1),
                    sdsf = SUB (\ beta -> r * (subf1g (b1 * beta))**(r-1) * sdsf1g (b2 * beta)) beta3}
           else error "analyzeExpr/ComposePower: condition (r >= 1 && g(x) > 0) not satisfied"
    Exp r i ->
      let x = row !! i
      in AR {fx = exp (r * x),
             subf = SUB (const $ exp (r * x)) (abs r),
             sdsf = SUB (const $ abs r * exp (r * x)) (abs r)}
    PowerLN i r ->
      let x = row !! i
      in AR {fx = x ** r,
             subf = SUB (const $ x ** r) (abs r),
             sdsf = SUB (const $ abs r * x ** r) (abs r)}
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
    ComposeL p es -> combineArsL p $ map (analyzeExpr row) es

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

combineArsL :: Double -> [AnalysisResult] -> AnalysisResult
combineArsL p ars =
  let fxs = map fx ars
      subfs = map subf ars
      sdsfs = map sdsf ars
      subfBetas = map subBeta subfs
      sdsfBetas = map subBeta sdsfs
      subgs = map subg subfs
      sdsgs = map subg sdsfs
  in AR {fx = lpnorm p fxs,
         subf = SUB (\ beta -> lpnorm p (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> maximum (map ($ beta) sdsgs)) (maximum sdsfBetas)}

analyzeTableExpr :: Table -> TableExpr -> AnalysisResult
analyzeTableExpr rows te =
  case te of
    SelectMin expr -> combineArsMin $ map (`analyzeExpr` expr) rows
    SelectMax expr -> combineArsMax $ map (`analyzeExpr` expr) rows
    SelectProd expr -> combineArsProd $ map (`analyzeExpr` expr) rows
    SelectL p expr -> combineArsL p $ map (`analyzeExpr` expr) rows

performAnalysis :: ProgramOptions -> Table -> TableExpr -> IO ()
performAnalysis args rows te = do
  let ar = analyzeTableExpr rows te
  putStrLn $ "Analysis result: " ++ show ar
  let epsilon = getEpsilon args
  printf "epsilon = %0.6f\n" epsilon
  printf "gamma = %0.6f\n" gamma
  let defaultBeta = epsilon / (2 * (gamma + 1))
  let fixedBeta = getBeta args
  let beta = chooseSUBBeta defaultBeta fixedBeta (sdsf ar)
  printf "beta = %0.6f\n" beta
  let b = epsilon / (gamma + 1) - beta
  printf "b = %0.6f\n" b
  let sds = subg (sdsf ar) beta
  printf "beta-smooth derivative sensitivity: %0.6f\n" sds
  let qr = fx ar
  printf "query result: %0.6f\n" qr
  let nl = sds / b
  printf "noise level: %0.6f\n" nl
  printf "relative error from noise: %0.3f%%\n" (nl / qr * 100)
