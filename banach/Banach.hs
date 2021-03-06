-- This module computes smooth derivative sensitivity in Banach spaces.
{-# LANGUAGE FlexibleInstances #-}
module Banach where

import ProgramOptions

import Prelude hiding ((!!))
import Data.List hiding ((!!))
import Data.Char
import Text.Printf
import Debug.Trace
import Control.Monad

import ErrorMsg hiding (at2)
import qualified ErrorMsg as EM (at2)
(!!) = EM.at2

type Var = Int                    -- variable corresponding to column i (starting from 0)

resultForAllTables :: String
resultForAllTables = "all input tables together"

-- this simultaneously defines a function E to be analyzed and a norm N on its domain
-- expressions of type Expr use values from a single row
data Expr = Power Var Double         -- x^r with norm | |
          | PowerLN Var Double       -- x^r with logarithmic norm: ||x|| = |ln x|, addition in Banach space is multiplication of real numbers
          | ComposePower Expr Double -- E^r with norm N
          | Exp Double Var           -- e^(r*x) with norm | |
          | ComposeExp Double Expr   -- e^(r*E) with norm N
          | Sigmoid Double Double Var-- s(a,c,x) = e^(a*(x-c))/(e^(a*(x-c)) + 1)
          | ComposeSigmoid Double Double Expr-- s(a,c,E) = e^(a*(E-c))/(e^(a*(E-c)) + 1)
          | Tauoid Double Double Var -- t(a,c,x) = 2/(e^(-a*(x-c)) + e^(a*(x-c)))
          | ComposeTauoid Double Double Expr-- t(a,c,E) = 2/(e^(-a*(E-c)) + e^(a*(E-c)))
          | L0Predicate Var (String -> String)-- p(x) with "l_0 norm": ||x||_0 = |x|^0 = 1 if x != 0 and 0 if x = 0
          | Const Double             -- constant c (real number, may be negative) in a zero-dimensional Banach space (with trivial norm)
          | ScaleNorm Double Expr    -- E with norm a * N
          | ZeroSens Expr            -- E with sensitivity forced to zero (the same as ScaleNorm with a -> infinity)
          | L Double [Var]           -- ||(x1,...,xn)||_p with l_p-norm
          | ComposeL Double [Expr]   -- ||(E1,...,En)||_p with norm ||(N1,...,Nn)||_p
          | LInf [Var]               -- same with p = infinity
          | Prod [Expr]              -- E1*...*En with norm ||(N1,...,Nn)||_1, no variable is used in more than one Ei
          | Prod2 [Expr]             -- E1*...*En with norm N, where N is the common norm of all Ei
          | Min [Expr]               -- min{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
          | Max [Expr]               -- max{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
          | Sump Double [Expr]       -- E1+...+En with norm ||(N1,...,Nn)||_p
          | SumInf [Expr]            -- E1+...+En with norm ||(N1,...,Nn)||_infinity
          | Sum2 [Expr]              -- E1+...+En with norm N, where N is the common norm of all Ei
          | Prec AnalysisResult      -- use precomputed AR for this node
          | StringCond String        -- we may want to leave some non-sensitive conditionals in string form
          | SigmoidPrecise Double Double Double Var         -- same as Sigmoid and ComposeSigmoid, but tries to delegate all noise to sensitivity
          | ComposeSigmoidPrecise Double Double Double Expr
          | TauoidPrecise Double Double Double Var         -- same as Tauoid and ComposeTauoid, but tries to delegate all noise to sensitivity
          | ComposeTauoidPrecise Double Double Double Expr
  deriving Show

instance Show (String -> String) where
  show f = "\\ x -> " ++ f "x"

-- expressions of type TableExpr use values from the whole table
data TableExpr = SelectProd [Expr]        -- product (map E rows) with norm ||(N1,...,Nn)||_1 where Ni is N applied to ith row
               | SelectMin [Expr]         -- min (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]
               | SelectMax [Expr]         -- max (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]
               | SelectL Double [Expr]    -- ||(E1,...,En)||_p with norm ||(N1,...,Nn)||_p
               | SelectSump Double [Expr] -- E1+...+En with norm ||(N1,...,Nn)||_p
               | SelectSumInf [Expr]      -- E1+...+En with norm ||(N1,...,Nn)||_infinity
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
                                           else error $ printf "ERROR (beta = %0.3f but must be >= %0.3f)" beta beta0

data AnalysisResult = AR {
  fx :: Double,             -- value of the analyzed function (f(x))
  subf :: SmoothUpperBound, -- smooth upper bound of the absolute value of the analyzed function itself
  sdsf :: SmoothUpperBound} -- smooth upper bound of the derivative sensitivity of the analyzed function
  deriving Show

unitSeparator :: Char
unitSeparator = chr 31

unitSeparator2 :: Char
unitSeparator2 = chr 30

unitSeparator3 :: Char
unitSeparator3 = chr 29

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
example2 = SelectMin [Prod [L 2 [0,1], ScaleNorm 20 $ PowerLN 2 (-1)]]

-- compute ||(x_1,...,x_n)||_p
lpnorm :: Double -> [Double] -> Double
lpnorm p xs = (sum $ map (**p) $ map abs xs) ** (1/p)

-- compute ||(x_1,...,x_n)||_q where || ||_q is the dual norm of || ||_p
lqnorm :: Double -> [Double] -> Double
lqnorm 1 xs = linfnorm xs
lqnorm p xs = lpnorm (dualnorm p) xs

-- compute ||(x_1,...,x_n)||_infinity
linfnorm :: [Double] -> Double
linfnorm = maximum . map abs

dualnorm :: Double -> Double
dualnorm p = p / (p-1)

-- return xs with the element (xs !! i) removed
skipith :: Int -> [a] -> [a]
skipith i xs = let (ys,_:zs) = splitAt i xs in ys ++ zs

analyzeExpr :: Row -> Expr -> AnalysisResult
analyzeExpr row expr = {-trace ("analyzeExpr " ++ show row ++ ": " ++ show expr ++ " -> " ++ show res)-} res where
 res =
  case expr of
    Prec ar   -> ar
    Power i r ->
      let x = row !! i
      in if r == 1
           then AR {fx = x,
                    subf = SUB (\ beta -> if abs x >= 1/beta then abs x else exp (beta * abs x - 1) / beta) 0,
                    sdsf = SUB (const 1) 0}
           else if r >= 1 && x > 0
             then AR {fx = x ** r,
                      subf = SUB (\ beta -> if x >= r/beta then x ** r else exp (beta*x - r) * (r/beta)**r) 0,
                      sdsf = SUB (\ beta -> if x >= (r-1)/beta then r * x**(r-1) else r * exp (beta*x - (r-1)) * ((r-1)/beta)**(r-1)) 0}
             else error "analyzeExpr/Power: condition (r >= 1 && x > 0 || r == 1) not satisfied"
    ComposePower e1 r ->
      let AR gx (SUB subf1g beta1) (SUB sdsf1g beta2) = analyzeExpr row e1
          beta3 = (r-1)*beta1 + beta2
          b1 = if beta3 > 0 then beta1 / beta3 else 1/r
          b2 = if beta3 > 0 then beta2 / beta3 else 1/r
      in if r >= 1 && gx > 0
           then AR {fx = gx ** r,
                    subf = SUB (\ beta -> subf1g (beta / r) ** r) (r*beta1),
                    sdsf = SUB (\ beta -> r * (subf1g (b1 * beta))**(r-1) * sdsf1g (b2 * beta)) beta3}
           else error "analyzeExpr/ComposePower: condition (r >= 1 && g(x) > 0) not satisfied"
    Exp r i ->
      let x = row !! i
      in AR {fx = exp (r * x),
             subf = SUB (const $ exp (r * x)) (abs r),
             sdsf = SUB (const $ abs r * exp (r * x)) (abs r)}
    ComposeExp r e1 ->
      let AR gx _ (SUB sdsf1g beta2) = analyzeExpr row e1
          b = sdsf1g 0
          f_x = exp (r * gx)
      in AR {fx = f_x,
             subf = SUB (const f_x) (abs r * b),
             sdsf = SUB (\ beta -> abs r * f_x * sdsf1g (beta - abs r * b)) (abs r * b + beta2)}
    Sigmoid a c i ->
      let x = row !! i
          y = exp (a * (x - c))
          z = y / (y + 1)
          a' = abs a
      in AR {fx = z,
             subf = SUB (const z) a',
             sdsf = SUB (const $ a' * y / (y+1)^2) a'}
    ComposeSigmoid a c e1 ->
      let AR gx _ (SUB sdsf1g beta2) = analyzeExpr row e1
          b = sdsf1g 0
          y = exp (a * (gx - c))
          z = y / (y + 1)
          a' = abs a
      in AR {fx = z,
             subf = SUB (const z) (a' * b),
             sdsf = SUB (\ beta -> a' * y / (y+1)^2 * sdsf1g (beta - a' * b)) (a' * b + beta2)}

    -- 'aa' is the actual sigmoid precision, 'ab' is the smoothness that we want
    SigmoidPrecise aa ab c i ->
      let x = row !! i
          y = exp (ab * (x - c))
          y' = exp (aa * (x - c))
          z  = y' / (y'+1)
          a' = abs ab
      in AR {fx = z,
             subf = SUB (const 1.0) 0,
             sdsf = SUB (const $ aa * y / (y+1)**2) a'}

    ComposeSigmoidPrecise aa ab c e1 ->
      let AR gx _ (SUB sdsf1g beta2) = analyzeExpr row e1
          b = sdsf1g 0
          y = exp (ab * (gx - c))
          y' = exp (aa * (gx - c))
          z = y' / (y' + 1)
          a' = abs ab
      in AR {fx = z,
             subf = SUB (const 1.0) 0,
             sdsf = SUB (\ beta -> aa * y / (y+1)**2 * sdsf1g (beta - a' * b)) (a' * b + beta2)}

    Tauoid a c i ->
      let x = row !! i
          y1 = exp (-a * (x - c))
          y2 = exp (a * (x - c))
          z = 2 / (y1 + y2)
          a' = abs a
      in AR {fx = z,
             subf = SUB (const z) a',
             sdsf = SUB (const $ a' * z) a'}
    ComposeTauoid a c e1 ->
      let AR gx _ (SUB sdsf1g beta2) = analyzeExpr row e1
          b = sdsf1g 0
          y1 = exp (-a * (gx - c))
          y2 = exp (a * (gx - c))
          z = 2 / (y1 + y2)
          a' = abs a
      in AR {fx = z,
             subf = SUB (const z) (a' * b),
             sdsf = SUB (\ beta -> a' * z * sdsf1g (beta - a' * b)) (a' * b + beta2)}

    TauoidPrecise aa ab c i ->
      let x = row !! i
          y1 = exp (-ab * (x - c))
          y2 = exp (ab * (x - c))
          y1' = exp (-aa * (x - c))
          y2' = exp (aa * (x - c))
          z = 2 / (y1' + y2')
          a' = abs ab
      in AR {fx = z,
             subf = SUB (const 1.0) 0,
             sdsf = SUB (const $ aa * 2 / (y1 + y2)) a'}
    ComposeTauoidPrecise aa ab c e1 ->
      let AR gx _ (SUB sdsf1g beta2) = analyzeExpr row e1
          b = sdsf1g 0
          y1 = exp (-ab * (gx - c))
          y2 = exp (ab * (gx - c))
          y1' = exp (-aa * (gx - c))
          y2' = exp (aa * (gx - c))
          z = 2 / (y1' + y2')
          a' = abs ab
      in AR {fx = z,
             subf = SUB (const 1.0) 0,
             sdsf = SUB (\ beta -> aa * 2 / (y1 + y2) * sdsf1g (beta - a' * b)) (a' * b + beta2)}

    PowerLN i r ->
      let x = row !! i
      in if x > 0
           then AR {fx = x ** r,
                    subf = SUB (const $ x ** r) (abs r),
                    sdsf = SUB (const $ abs r * x ** r) (abs r)}
           else error "analyzeExpr/PowerLN: condition (x > 0) not satisfied"
    Const c ->
      AR {fx = c,
          subf = SUB (const (abs c)) 0,
          sdsf = SUB (const 0) 0}
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
    Prod2 es -> combineArsProd2 $ map (analyzeExpr row) es
    Min es -> combineArsMin $ map (analyzeExpr row) es
    Max es -> combineArsMax $ map (analyzeExpr row) es
    ComposeL p es -> combineArsL p $ map (analyzeExpr row) es
    Sump p es -> combineArsSump p $ map (analyzeExpr row) es
    SumInf es -> combineArsSumInf $ map (analyzeExpr row) es
    Sum2 es -> combineArsSum2 $ map (analyzeExpr row) es

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
      c i beta = let s = ((sdsgs !! i) beta) in if s == 0 then 0 else s * product (map ($ beta) $ skipith i subgs)
  in AR {fx = product fxs,
         subf = SUB (\ beta -> product (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> linfnorm (map (\ i -> c i beta) [0..n-1])) (maximum (subfBetas ++ sdsfBetas))}

combineArsProd2 :: [AnalysisResult] -> AnalysisResult
combineArsProd2 ars =
  let fxs = map fx ars
      subfs = map subf ars
      sdsfs = map sdsf ars
      subfBetas = map subBeta subfs
      sdsfBetas = map subBeta sdsfs
      subgs = map subg subfs
      sdsgs = map subg sdsfs
      n = length ars
      divByn x = x / fromIntegral n
      c i beta = ((sdsgs !! i) (divByn beta)) * product (map ($ (divByn beta)) $ skipith i subgs)
  in AR {fx = product fxs,
         subf = SUB (\ beta -> product (map ($ (divByn beta)) subgs)) (sum subfBetas),
         sdsf = SUB (\ beta -> sum (map (\ i -> c i beta) [0..n-1])) (sum subfBetas + maximum (zipWith (-) sdsfBetas subfBetas))}

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

-- the computed function is l_p-norm but the norm is l_infinity
combineArsLpInf :: Double -> [AnalysisResult] -> AnalysisResult
combineArsLpInf p ars =
  let fxs = map fx ars
      subfs = map subf ars
      sdsfs = map sdsf ars
      subfBetas = map subBeta subfs
      sdsfBetas = map subBeta sdsfs
      subgs = map subg subfs
      sdsgs = map subg sdsfs
  in AR {fx = lpnorm p fxs,
         subf = SUB (\ beta -> lpnorm p (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> lpnorm 1 (map ($ beta) sdsgs)) (maximum sdsfBetas)}

combineArsSump :: Double -> [AnalysisResult] -> AnalysisResult
combineArsSump p ars =
  let fxs = map fx ars
      subfs = map subf ars
      sdsfs = map sdsf ars
      subfBetas = map subBeta subfs
      sdsfBetas = map subBeta sdsfs
      subgs = map subg subfs
      sdsgs = map subg sdsfs
  in AR {fx = sum fxs,
         subf = SUB (\ beta -> sum (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> lqnorm p (map ($ beta) sdsgs)) (maximum sdsfBetas)}

combineArsSumInf :: [AnalysisResult] -> AnalysisResult
combineArsSumInf ars =
  let fxs = map fx ars
      subfs = map subf ars
      sdsfs = map sdsf ars
      subfBetas = map subBeta subfs
      sdsfBetas = map subBeta sdsfs
      subgs = map subg subfs
      sdsgs = map subg sdsfs
  in AR {fx = sum fxs,
         subf = SUB (\ beta -> sum (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> lpnorm 1 (map ($ beta) sdsgs)) (maximum sdsfBetas)}

combineArsSum2 :: [AnalysisResult] -> AnalysisResult
combineArsSum2 ars =
  let fxs = map fx ars
      subfs = map subf ars
      sdsfs = map sdsf ars
      subfBetas = map subBeta subfs
      sdsfBetas = map subBeta sdsfs
      subgs = map subg subfs
      sdsgs = map subg sdsfs
  in AR {fx = sum fxs,
         subf = SUB (\ beta -> sum (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> sum (map ($ beta) sdsgs)) (maximum sdsfBetas)}

-- the parameter cs sets each row into a class,
-- the rows in the same class must be combined with l_infinity norm,
-- different classes are combined with the specified norm,
-- rows in class -1 are nonsensitive
analyzeTableExpr :: Table -> [Int] -> TableExpr -> AnalysisResult
analyzeTableExpr rows cs te =
  case te of
    SelectMin [expr] | n /= 1 -> analyzeTableExpr rows cs (SelectMin $ map (const expr) rows)
    SelectMax [expr] | n /= 1 -> analyzeTableExpr rows cs (SelectMax $ map (const expr) rows)
    SelectProd [expr] | n /= 1 -> analyzeTableExpr rows cs (SelectProd $ map (const expr) rows)
    SelectL p [expr] | n /= 1 -> analyzeTableExpr rows cs (SelectL p $ map (const expr) rows)
    SelectSump p [expr] | n /= 1 -> analyzeTableExpr rows cs (SelectSump p $ map (const expr) rows)
    SelectSumInf [expr] | n /= 1 -> analyzeTableExpr rows cs (SelectSumInf $ map (const expr) rows)
    SelectMin exprs -> combineArsMin $ zipWith analyzeExpr rows (addZeroSens exprs)
    SelectMax exprs -> combineArsMax $ zipWith analyzeExpr rows (addZeroSens exprs)
    SelectProd exprs ->
      combineArsProd $
        flip map (groupRows rows exprs cs) $ \ (c,re) ->
          combineArsProd2 $ map (\ (r,e) -> analyzeExpr r (if c == -1 then ZeroSens e else e)) re
    SelectL p exprs ->
      combineArsL p $
        flip map (groupRows rows exprs cs) $ \ (c,re) ->
          combineArsLpInf p $ map (\ (r,e) -> analyzeExpr r (if c == -1 then ZeroSens e else e)) re
    SelectSump p exprs ->
      combineArsSump p $
        flip map (groupRows rows exprs cs) $ \ (c,re) ->
          combineArsSumInf $ map (\ (r,e) -> analyzeExpr r (if c == -1 then ZeroSens e else e)) re
    SelectSumInf exprs -> combineArsSumInf $ zipWith analyzeExpr rows (addZeroSens exprs)
  where
    n = length rows
    groupRows :: Table -> [Expr] -> [Int] -> [(Int, [(Row,Expr)])]
    groupRows rows es cs = map (\ g -> (fst (head g), map snd g)) $ groupBy (\ x y -> fst x == fst y) $ sortBy (\ x y -> compare (fst x) (fst y)) $ zip cs (zip rows es)
    addZeroSens exprs = zipWith (\ c e -> if c == -1 then ZeroSens e else e) cs exprs

-- simulate the old behavior of analyzeTableExpr
analyzeTableExprOld :: Table -> TableExpr -> AnalysisResult
analyzeTableExprOld rows te = analyzeTableExpr rows [0..length rows - 1] te

sumGroupsWith :: (Ord a, Ord b) => ([b] -> b) -> [(a,b)] -> [(a,b)]
sumGroupsWith sumf = map (\ g -> (fst (head g), sumf (map snd g))) . groupBy (\ x y -> fst x == fst y) . sort

-- added an input taskMap that is used to generate some intermediate results for each task
performAnalyses :: ProgramOptions -> Table -> String -> Double -> [(String,[Int])] -> [(String, String, [Int], TableExpr)] -> IO ()
performAnalyses args rows outputTableName qr taskMap tableExprData = do
  let debug = not (alternative args)
  res0 <- forM tableExprData $ \ (tableName, tableAlias, cs, te) -> do
    when debug $ putStrLn ""
    when debug $ putStrLn "--------------------------------"
    when debug $ putStrLn $ "=== Analyzing table " ++ tableName ++ " of " ++ tableAlias ++ " ==="

    result <- performAnalysis args rows cs te
    return (tableName, result)

  --let res = sumGroupsWith sum res0
  when debug $ putStrLn ""
  when debug $ putStrLn "--------------------------------"
  when debug $ putStrLn "Analysis summary (sensitivities w.r.t. each table):"
  --if alternative args
  --  then putStr $ intercalate [unitSeparator] $ concat $ map (\ (tableName, sds) -> [tableName, show sds]) res
  --  else forM_ res $ \ (tableName, sds) -> printf "%s: %0.6f\n" tableName sds

  -- partition the result among tasks, apply sumGroupsWith for each task
  -- covert to a properly formatted string, let the tasks be separated by a special character 30
  -- when combining table copies, we take maximal noise level since it correpons to maximal beta
  let taskAggr0 = map (\(taskName,is) -> (taskName, sumGroupsWith (foldr (\(x1,y1) (x2,y2) -> (max x1 x2, y1 + y2)) (0,0)) $ map (res0 !!) is)) taskMap

  -- add an aggregated result to the output, sum up the sensitivities and take time minimal b
  let taskAggr = map (\(taskName,vs) ->
                         if taskName == outputTableName then
                             let v = foldr (\(x1,y1) (x2,y2) -> (max x1 x2, y1 + y2)) (0,0) (snd $ unzip vs) in
                             (taskName, (resultForAllTables, v):vs)
                         else (taskName,vs)
                     ) taskAggr0

  let taskStr = if alternative args then
          map (\(taskName,res) -> taskName ++ [unitSeparator] ++
                  (intercalate [unitSeparator] $ concat $ map (\ (tableName, (b,sds)) -> [tableName, show sds, show qr, show (sds/b), show ((sds/b) / qr * 100)]) res)) taskAggr
      else
          map (\(taskName,res) -> taskName ++ "\n" ++
                  (intercalate "\n" $ map (\ (tableName, (b,sds)) -> printf "%s: %0.6f\t %0.6f\t %0.6f\t %0.3f" tableName qr (sds/b) sds ((sds/b) / qr * 100)) res)) taskAggr
  putStrLn $ intercalate (if alternative args then [unitSeparator2] else "\n\n") taskStr

-- this now also outputs b, we need it to compute all errors
--performAnalysis :: ProgramOptions -> Table -> [Int] -> TableExpr -> IO Double
performAnalysis :: ProgramOptions -> Table -> [Int] -> TableExpr -> IO (Double,Double)
performAnalysis args rows cs te = do
  let debug = not (alternative args)
  let ar = analyzeTableExpr rows cs te
  when debug $ putStrLn $ "Analysis result: " ++ show ar
  let epsilon = getEpsilon args
  when debug $ printf "epsilon = %0.6f\n" epsilon
  when debug $ printf "gamma = %0.6f\n" gamma
  let defaultBeta = epsilon / (2 * (gamma + 1))
  let fixedBeta = getBeta args
  let beta = chooseSUBBeta defaultBeta fixedBeta (sdsf ar)
  when debug $ printf "beta = %0.6f\n" beta
  let b = epsilon / (gamma + 1) - beta
  when debug $ printf "b = %0.6f\n" b
  let sds = subg (sdsf ar) beta
  when debug $ printf "beta-smooth derivative sensitivity: %0.6f\n" sds
  let qr = fx ar
  when debug $ printf "query result: %0.6f\n" qr
  let nl = sds / b
  when debug $ printf "noise level: %0.6f\n" nl
  when debug $ printf "relative error from noise: %0.3f%%\n" (nl / qr * 100)
  --when debug $ when (nl < 0) $ putStrLn "NEGATIVE NOISE LEVEL - differential privacy could not be achieved, try to increase epsilon!"
  when (nl < 0) $ error error_negativeNoise
  return (b,sds)
--  return sds

