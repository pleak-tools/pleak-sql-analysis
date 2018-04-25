{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, RebindableSyntax, FlexibleInstances #-}

module BanachQ where

import Banach (Expr(..), TableExpr(..), (!!), chooseBeta, chooseBetaCustom, gamma, dualnorm, skipith)
import ProgramOptions

import qualified Prelude as P
import qualified Data.List as L
import Prelude hiding (fromInteger,fromRational,(!!),(+),(-),(*),(/),(**),(==),(/=),(<=),(>=),(<),(>),exp,abs,sum,product,minimum,maximum)
import Data.List hiding ((!!),sum,product,minimum,maximum)
import Text.Printf
import Control.Monad

fromInteger :: Integer -> Double
fromInteger = P.fromInteger

fromRational :: Rational -> Double
fromRational = P.fromRational

data ExprQ = Q Double                -- a constant
           | VarQ String             -- a variable
           | FunQ String ExprQ       -- an SQL function
           | OpQ String ExprQ ExprQ  -- an SQL binary operator
           | ListFunQ String [ExprQ] -- an SQL function with argument list
           | IfThenElseQ BoolExprQ ExprQ ExprQ
           | (:+) ExprQ ExprQ
           | (:-) ExprQ ExprQ
           | (:*) ExprQ ExprQ
           | (:/) ExprQ ExprQ
           | (:**) ExprQ ExprQ        -- exponentiation
           | Select ExprQ String String -- SELECT x FROM y WHERE z

data BoolExprQ = CmpOpQ String ExprQ ExprQ -- an SQL comparison operator

infix 4 ==
infix 4 /=
infix 4 <=
infix 4 >=
infix 4 <
infix 4 >
infixl 6 +
infixl 6 -
infixl 7 *
infixl 7 /
infixr 8 **

class Arith1Q a where
  exp,abs :: a -> a
  sum,product,minimum,maximum :: [a] -> a

instance Arith1Q Double where
  exp = P.exp
  abs = P.abs
  sum = L.sum
  product = L.product
  minimum = L.minimum
  maximum = L.maximum

instance Arith1Q ExprQ where
  exp = expQ
  abs = absQ
  sum = sumQ
  product = productQ
  minimum = minimumQ
  maximum = maximumQ

class ArithQ a b c | a b -> c where
  (+),(-),(*),(/),(**) :: a -> b -> c

instance ArithQ Double Double Double where
  (+) = (P.+)
  (-) = (P.-)
  (*) = (P.*)
  (/) = (P./)
  (**) = (P.**)

instance ArithQ ExprQ ExprQ ExprQ where
  (+) = (:+)
  (-) = (:-)
  (*) = (:*)
  (/) = (:/)
  (**) = (:**)

instance ArithQ Double ExprQ ExprQ where
  x + y = Q x :+ y
  x - y = Q x :- y
  x * y = Q x :* y
  x / y = Q x :/ y
  x ** y = Q x :** y

instance ArithQ ExprQ Double ExprQ where
  x + y = x :+ Q y
  x - y = x :- Q y
  x * y = x :* Q y
  x / y = x :/ Q y
  x ** y = x :** Q y

class CmpQ a b c | a b -> c where
  (==),(/=),(<=),(>=),(<),(>) :: a -> b -> c

instance CmpQ Double Double Bool where
  (==) = (P.==)
  (/=) = (P./=)
  (<=) = (P.<=)
  (>=) = (P.>=)
  (<) = (P.<)
  (>) = (P.>)

instance CmpQ ExprQ ExprQ BoolExprQ where
  (==) = CmpOpQ "="
  (/=) = CmpOpQ "!="
  (<=) = CmpOpQ "<="
  (>=) = CmpOpQ ">="
  (<) = CmpOpQ "<"
  (>) = CmpOpQ ">"

instance CmpQ Double ExprQ BoolExprQ where
  x == y = Q x == y
  x /= y = Q x /= y
  x <= y = Q x <= y
  x >= y = Q x >= y
  x < y = Q x < y
  x > y = Q x > y

instance CmpQ ExprQ Double BoolExprQ where
  x == y = x == Q y
  x /= y = x /= Q y
  x <= y = x <= Q y
  x >= y = x >= Q y
  x < y = x < Q y
  x > y = x > Q y

class IfThenElseQ a b where
  ifThenElse :: a -> b -> b -> b

instance IfThenElseQ Bool a where
  ifThenElse True x y = x
  ifThenElse False x y = y

instance IfThenElseQ BoolExprQ ExprQ where
  ifThenElse = IfThenElseQ

instance IfThenElseQ BoolExprQ AnalysisResult where
  ifThenElse b x err = x -- TODO: handle the error message correctly

expQ = FunQ "exp"
logQ = FunQ "log"
absQ = FunQ "abs"

minimumT = FunQ "min"
maximumT = FunQ "max"
sumT = FunQ "sum"
productT = expQ . sumT . logQ

minimumQ = ListFunQ "least"
maximumQ = ListFunQ "greatest"

sumQ = foldl1 (:+)
productQ = foldl1 (:*)

-- forces the type of a number literal to be Double
--dbl :: Double -> Double
--dbl = id

instance Show ExprQ where
  show (Q x) = show x
  show (VarQ x) = x
  show (FunQ f x) = f ++ '(' : show x ++ ")"
  show (OpQ op x y) = '(' : show x ++ ' ' : op ++ ' ' : show y ++ ")"
  show (ListFunQ f xs) = f ++ '(' : intercalate ", " (map show xs) ++ ")"
  show (IfThenElseQ b x y) = "case when " ++ show b ++ " then " ++ show x ++ " else " ++ show y ++ " end"
  show (x :+ y) = '(' : show x ++ " + " ++ show y ++ ")"
  show (x :- y) = '(' : show x ++ " - " ++ show y ++ ")"
  show (x :* y) = '(' : show x ++ " * " ++ show y ++ ")"
  show (x :/ y) = '(' : show x ++ " / " ++ show y ++ ")"
  show (x :** y) = '(' : show x ++ " ^ " ++ show y ++ ")"
  show (Select x fr wh) = "SELECT " ++ show x ++ (if null fr then "" else " FROM ") ++ fr ++ (if null wh then "" else " WHERE ") ++ wh ++ ";"

instance Show BoolExprQ where
  show (CmpOpQ op x y) = '(' : show x ++ ' ' : op ++ ' ' : show y ++ ")"

data SmoothUpperBound = SUB {
  subg :: Double -> ExprQ,
  subBeta :: Double}

instance Show SmoothUpperBound where
  show (SUB g beta0) = let beta = chooseBeta beta0
                       in if beta >= beta0 then (printf "%s (beta = %0.3f)" (show (g beta)) beta :: String)
                                           else ((error $ printf "ERROR (beta = %0.3f but must be >= %0.3f)" beta beta0) :: String)

data AnalysisResult = AR {
  fx :: ExprQ,             -- value of the analyzed function (f(x))
  subf :: SmoothUpperBound, -- smooth upper bound of the absolute value of the analyzed function itself
  sdsf :: SmoothUpperBound} -- smooth upper bound of the derivative sensitivity of the analyzed function
  deriving Show

chooseSUBBeta :: Double -> Maybe Double -> SmoothUpperBound -> Double
chooseSUBBeta defaultBeta fixedBeta (SUB g beta0) =
                              let beta = chooseBetaCustom defaultBeta fixedBeta beta0
                              in if beta >= beta0 then beta
                                                  else error $ printf "ERROR (beta = %0.3f but must be >= %0.3f)" beta beta0

-- compute ||(x_1,...,x_n)||_p
lpnorm :: Double -> [ExprQ] -> ExprQ
lpnorm p xs = (sum $ map (** p) $ map abs xs) ** (1 / p)

lpnormT :: Double -> ExprQ -> ExprQ
lpnormT p xs = (sumT $ (abs xs) ** p) ** (1 / p)

-- compute ||(x_1,...,x_n)||_q where || ||_q is the dual norm of || ||_p
lqnorm :: Double -> [ExprQ] -> ExprQ
lqnorm 1 xs = linfnorm xs
lqnorm p xs = lpnorm (dualnorm p) xs

lqnormT :: Double -> ExprQ -> ExprQ
lqnormT 1 = linfnormT
lqnormT p = lpnormT (dualnorm p)

-- compute ||(x_1,...,x_n)||_infinity
linfnorm :: [ExprQ] -> ExprQ
linfnorm = maximumQ . map absQ

linfnormT :: ExprQ -> ExprQ
linfnormT = maximumT . absQ

analyzeExprQ :: [String] -> Expr -> AnalysisResult
analyzeExprQ colNames = analyzeExpr (map VarQ colNames)

analyzeExpr :: [ExprQ] -> Expr -> AnalysisResult
analyzeExpr row expr = res where
 res =
  case expr of
    Power i r ->
      let x = row !! i
      in if r == 1
           then AR {fx = x,
                    subf = SUB (\ beta -> ifThenElse (abs x >= 1 / beta) (abs x) (exp (beta * abs x - 1) / beta)) 0,
                    sdsf = SUB (const (Q 1)) 0}
           else if r >= 1
             then if x > 0
                   then AR {fx = x ** r,
                            subf = SUB (\ beta -> ifThenElse (x >= r/beta) (x ** r) (exp (beta*x - r) * (r/beta)**r)) 0,
                            sdsf = SUB (\ beta -> ifThenElse (x >= (r-1)/beta) (r * x**(r-1)) (r * exp (beta*x - (r-1)) * ((r-1)/beta)**(r-1))) 0}
                   else error "analyzeExpr/Power: condition (r >= 1 && x > 0 || r == 1) not satisfied"
             else error "analyzeExpr/Power: condition (r >= 1 && x > 0 || r == 1) not satisfied"
    Exp r i ->
      let x = row !! i
      in AR {fx = exp (r * x),
             subf = SUB (const $ exp (r * x)) (abs r),
             sdsf = SUB (const $ abs r * exp (r * x)) (abs r)}
    Sigmoid a c i ->
      let x = row !! i
          y = exp (a * (x - c))
          z = y / (y + 1)
          a' = abs a
      in AR {fx = z,
             subf = SUB (const z) a',
             sdsf = SUB (const $ a' * y / (y+1)**2) a'}
    Tauoid a c i ->
      let x = row !! i
          y1 = exp ((-a) * (x - c))
          y2 = exp (a * (x - c))
          z = 2 / (y1 + y2)
          a' = abs a
      in AR {fx = z,
             subf = SUB (const z) a',
             sdsf = SUB (const $ a' * z) a'}
    PowerLN i r ->
      let x = row !! i
      in if x > 0
           then AR {fx = x ** r,
                    subf = SUB (const $ x ** r) (abs r),
                    sdsf = SUB (const $ abs r * x ** r) (abs r)}
           else error "analyzeExpr/PowerLN: condition (x > 0) not satisfied"
    Const c ->
      AR {fx = Q c,
          subf = SUB (const (Q $ abs c)) 0,
          sdsf = SUB (const (Q 0)) 0}
    ScaleNorm a e1 ->
      let AR fx1 (SUB subf1g subf1beta) (SUB sdsf1g sdsf1beta) = analyzeExpr row e1
      in AR {fx = fx1,
             subf = SUB (\ beta -> subf1g (beta*a)) (subf1beta/a),
             sdsf = SUB (\ beta -> sdsf1g (beta*a) / a) (sdsf1beta/a)}
    ZeroSens e1 ->
      let AR fx1 (SUB subf1g subf1beta) (SUB sdsf1g sdsf1beta) = analyzeExpr row e1
      in AR {fx = fx1,
             subf = SUB (const fx1) 0,
             sdsf = SUB (const (Q 0)) 0}
    L p is ->
      let xs = map (row !!) is
          y = lpnorm p xs
      in AR {fx = y,
             subf = SUB (\ beta -> if y >= 1/beta then y else exp (beta * y - 1) / beta) 0,
             sdsf = SUB (const (Q 1)) 0}
    LInf is ->
      let xs = map (row !!) is
          y = linfnorm xs
      in AR {fx = y,
             subf = SUB (\ beta -> if y >= 1/beta then y else exp (beta * y - 1) / beta) 0,
             sdsf = SUB (const (Q 1)) 0}
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
      c i beta = let s = ((sdsgs !! i) beta) in if s == 0 then Q 0 else s * product (map ($ beta) $ skipith i subgs)
  in AR {fx = product fxs,
         subf = SUB (\ beta -> product (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> linfnorm (map (\ i -> c i beta) [round 0..n P.- round 1])) (maximum (subfBetas ++ sdsfBetas))}

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
      divByn :: Double -> Double
      divByn x = x / (fromIntegral n :: Double)
      c i beta = ((sdsgs !! i) (divByn beta)) * product (map ($ (divByn beta)) $ skipith i subgs)
  in AR {fx = product fxs,
         subf = SUB (\ beta -> product (map ($ (divByn beta)) subgs)) (sum subfBetas),
         sdsf = SUB (\ beta -> sum (map (\ i -> c i beta) [round 0..n P.- round 1])) (sum subfBetas + maximum (zipWith (-) sdsfBetas subfBetas))}

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

combineArsMinT :: AnalysisResult -> AnalysisResult
combineArsMinT ar =
  AR {fx = minimumT (fx ar),
      subf = SUB (\ beta -> minimumT (subg (subf ar) beta)) (subBeta (subf ar)),
      sdsf = SUB (\ beta -> maximumT (subg (sdsf ar) beta)) (subBeta (sdsf ar))}

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

combineArsMaxT :: AnalysisResult -> AnalysisResult
combineArsMaxT ar =
  AR {fx = maximumT (fx ar),
      subf = SUB (\ beta -> maximumT (subg (subf ar) beta)) (subBeta (subf ar)),
      sdsf = SUB (\ beta -> maximumT (subg (sdsf ar) beta)) (subBeta (sdsf ar))}

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

combineArsLT :: Double -> AnalysisResult -> AnalysisResult
combineArsLT p ar =
  AR {fx = lpnormT p (fx ar),
      subf = SUB (\ beta -> lpnormT p (subg (subf ar) beta)) (subBeta (subf ar)),
      sdsf = SUB (\ beta -> maximumT (subg (sdsf ar) beta)) (subBeta (sdsf ar))}

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

combineArsLpInfT :: Double -> AnalysisResult -> AnalysisResult
combineArsLpInfT p ar =
  AR {fx = lpnormT p (fx ar),
      subf = SUB (\ beta -> lpnormT p (subg (subf ar) beta)) (subBeta (subf ar)),
      sdsf = SUB (\ beta -> lpnormT 1 (subg (sdsf ar) beta)) (subBeta (sdsf ar))}

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

combineArsSumpT :: Double -> AnalysisResult -> AnalysisResult
combineArsSumpT p ar =
  AR {fx = sumT (fx ar),
      subf = SUB (\ beta -> sumT (subg (subf ar) beta)) (subBeta (subf ar)),
      sdsf = SUB (\ beta -> lqnormT p (subg (sdsf ar) beta)) (subBeta (sdsf ar))}

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

combineArsSumInfT :: AnalysisResult -> AnalysisResult
combineArsSumInfT ar =
  AR {fx = sumT (fx ar),
      subf = SUB (\ beta -> sumT (subg (subf ar) beta)) (subBeta (subf ar)),
      sdsf = SUB (\ beta -> lpnormT 1 (subg (sdsf ar) beta)) (subBeta (sdsf ar))}

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

analyzeTableExpr :: [String] -> TableExpr -> AnalysisResult
analyzeTableExpr cols te =
  case te of
    SelectMin (expr : _) -> combineArsMinT (analyzeExprQ cols expr)
    SelectMax (expr : _) -> combineArsMaxT (analyzeExprQ cols expr)
    SelectL p (expr : _) -> combineArsLT p (analyzeExprQ cols expr)
    SelectSump p (expr : _) -> combineArsSumpT p (analyzeExprQ cols expr)
    SelectSumInf (expr : _) -> combineArsSumInfT (analyzeExprQ cols expr)

-- SELECT expr FROM fr WHERE wh
-- (colNames !! i) is the name of the variable with number i in expr
-- fr may contain multiple tables and aliases, e.g. "t as t1, t as t2, t3"
-- wh is the WHERE condition as a string, e.g. "t1.c1 = t2.c1 AND t1.c2 >= t2.c2"
analyzeTableExprQ :: String -> String -> [String] -> TableExpr -> AnalysisResult
analyzeTableExprQ fr wh colNames te =
  let AR fx1 (SUB subf1g subf1beta) (SUB sdsf1g sdsf1beta) = analyzeTableExpr colNames te
  in AR (Select fx1 fr wh) (SUB ((\ x -> Select x fr wh) . subf1g) subf1beta) (SUB ((\ x -> Select x fr wh) . sdsf1g) sdsf1beta)

performAnalyses :: ProgramOptions -> [String] -> String -> Double -> [(String,[Int])] -> [(String, [Int], TableExpr)] -> IO ()
performAnalyses args colNames outputTableName qr taskMap tableExprData = do
  let debug = not (alternative args)
  let (tableNames,_,_) = unzip3 tableExprData
  let fromPart = intercalate ", " tableNames
  let wherePart = ""
  forM_ tableExprData $ \ (tableName, cs, te) -> do
    when debug $ putStrLn ""
    when debug $ putStrLn "--------------------------------"
    when debug $ putStrLn $ "=== Analyzing table " ++ tableName ++ " ==="
    let ar = analyzeTableExprQ fromPart wherePart colNames te
    putStrLn "Analysis result:"
    print ar
    let epsilon = getEpsilon args
    when debug $ printf "epsilon = %0.6f\n" epsilon
    when debug $ printf "gamma = %0.6f\n" gamma
    let defaultBeta = epsilon / (2 * (gamma + 1))
    let fixedBeta = getBeta args
    let beta = chooseSUBBeta defaultBeta fixedBeta (sdsf ar)
    when debug $ printf "beta = %0.6f\n" beta
    let b = epsilon / (gamma + 1) - beta
    when debug $ printf "b = %0.6f\n" b
    let qr = fx ar
    when debug $ putStrLn "Query result:"
    when debug $ print qr
    let sds = subg (sdsf ar) beta
    when debug $ putStrLn "beta-smooth derivative sensitivity:"
    when debug $ print sds
