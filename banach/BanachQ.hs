{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, RebindableSyntax, FlexibleInstances #-}

module BanachQ where

import Banach (Expr(..), TableExpr(..), (!!), chooseBeta, chooseBetaCustom, gamma, dualnorm, skipith)
import qualified Banach as B
import ProgramOptions
import CreateTablesQ

import qualified Prelude as P
import qualified Data.List as L
import Prelude hiding (fromInteger,fromRational,(!!),(+),(-),(*),(/),(**),(==),(/=),(<=),(>=),(<),(>),exp,abs,sum,product,minimum,maximum)
import Data.List hiding ((!!),sum,product,minimum,maximum)
import Data.List.Split
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
           | GroupBy ExprQ String String -- x GROUP BY y HAVING z
           | ExprQ `As` String        -- x AS y
           | ExprQ `Where` String     -- x WHERE y
           | Subquery ExprQ ExprQ     -- SELECT x FROM (subquery y)

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
  show (Q x) | x >= 0    = show x
             | otherwise = '(' : show x ++ ")"
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
  show (Select (Subquery x y) fr wh) = show (Subquery x (Select y fr wh))
  show (Select (GroupBy (x `Where` y) g h) fr wh) = show (Select (GroupBy x g h) fr ('(' : wh ++ ") AND " ++ y))
  show (Select (GroupBy x g h) fr wh) = "SELECT " ++ show x ++
                                        (if null fr then "" else " FROM ") ++ fr ++ (if null wh then "" else " WHERE ") ++ wh ++
                                        " GROUP BY " ++ g ++ (if null h then "" else " HAVING ") ++ h
  show (Select (x `Where` y) fr wh) = show (Select x fr ('(' : wh ++ ") AND " ++ y))
  show (Select x fr wh) = "SELECT " ++ show x ++ (if null fr then "" else " FROM ") ++ fr ++ (if null wh then "" else " WHERE ") ++ wh
  show (GroupBy x g h) = show x ++ " GROUP BY " ++ g ++ (if null h then "" else " HAVING ") ++ h
  show (x `As` a) = show x ++ " AS " ++ a
  show (Subquery x y) = "SELECT " ++ show x ++ " FROM (" ++ show y ++ ") AS sub"

instance Show BoolExprQ where
  show (CmpOpQ op x y) = '(' : show x ++ ' ' : op ++ ' ' : show y ++ ")"

data SmoothUpperBound = SUB {
  subg :: Double -> ExprQ,
  subBeta :: Double}

instance Show SmoothUpperBound where
  show (SUB g beta0)
        | beta0 >= 0 = let beta = chooseBeta beta0
                       in if beta >= beta0 then (printf "%s (beta = %0.3f)" (show (g beta)) beta :: String)
                                           else ((error $ printf "ERROR (beta = %0.3f but must be >= %0.3f)" beta beta0) :: String)
        | otherwise  = "unknown"

data AnalysisResult = AR {
  fx :: ExprQ,             -- value of the analyzed function (f(x))
  subf :: SmoothUpperBound, -- smooth upper bound of the absolute value of the analyzed function itself
  sdsf :: SmoothUpperBound, -- smooth upper bound of the derivative sensitivity of the analyzed function
  gub :: Double,            -- global (constant) upper bound on the absolute value of the analyzed function itself
  gsens :: Double}          -- (upper bound on) global sensitivity of the analyzed function, may be infinity
  deriving Show

infinity :: Double
infinity = 1/0

unknownSUB = SUB undefined (-1)

aR :: AnalysisResult
aR = AR {subf = unknownSUB, gub = infinity, gsens = infinity}

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
    Prec (B.AR fx (B.SUB subg subBeta) (B.SUB sdsg sdsBeta)) -> AR {fx = Q fx, subf = SUB (Q . subg) subBeta, sdsf = SUB (Q . subg) subBeta,
                                                                    gub = if subBeta > 0 then infinity else subg 0,
                                                                    gsens = if sdsBeta > 0 then infinity else sdsg 0}
    Power i r ->
      let x = row !! i
      in if r == 1
           then aR {fx = x,
                    subf = SUB (\ beta -> ifThenElse (abs x >= 1 / beta) (abs x) (exp (beta * abs x - 1) / beta)) 0,
                    sdsf = SUB (const (Q 1)) 0,
                    gsens = 1}
           else if r >= 1
             then if x > 0
                   then aR {fx = x ** r,
                            subf = SUB (\ beta -> ifThenElse (x >= r/beta) (x ** r) (exp (beta*x - r) * (r/beta)**r)) 0,
                            sdsf = SUB (\ beta -> ifThenElse (x >= (r-1)/beta) (r * x**(r-1)) (r * exp (beta*x - (r-1)) * ((r-1)/beta)**(r-1))) 0}
                   else error "analyzeExpr/Power: condition (r >= 1 && x > 0 || r == 1) not satisfied"
             else error "analyzeExpr/Power: condition (r >= 1 && x > 0 || r == 1) not satisfied"
    ComposePower e1 r ->
      let AR gx (SUB subf1g beta1) (SUB sdsf1g beta2) gub _ = analyzeExpr row e1
          beta3 = (r-1)*beta1 + beta2
          b1 = if beta3 > 0 then beta1 / beta3 else 1/r
          b2 = if beta3 > 0 then beta2 / beta3 else 1/r
      in if r >= 1
           then if gx > 0
                 then AR {fx = gx ** r,
                          subf = SUB (\ beta -> subf1g (beta / r) ** r) (r*beta1),
                          sdsf = SUB (\ beta -> r * (subf1g (b1 * beta))**(r-1) * sdsf1g (b2 * beta)) beta3,
                          gub = gub ** r}
                 else error "analyzeExpr/ComposePower: condition (r >= 1 && g(x) > 0) not satisfied"
           else error "analyzeExpr/ComposePower: condition (r >= 1 && g(x) > 0) not satisfied"
    Exp r i ->
      let x = row !! i
      in aR {fx = exp (r * x),
             subf = SUB (const $ exp (r * x)) (abs r),
             sdsf = SUB (const $ abs r * exp (r * x)) (abs r)}
    ComposeExp r e1 ->
      let AR gx _ (SUB sdsf1g beta2) gub gsens = analyzeExpr row e1
          b = gsens
          f_x = exp (r * gx)
      in AR {fx = f_x,
             subf = SUB (const f_x) (abs r * b),
             sdsf = SUB (\ beta -> abs r * f_x * sdsf1g (beta - abs r * b)) (abs r * b + beta2),
             gub = exp (abs r * gub)}
    Sigmoid a c i ->
      let x = row !! i
          y = exp (a * (x - c))
          z = y / (y + 1)
          a' = abs a
      in aR {fx = z,
             subf = SUB (const z) a',
             sdsf = SUB (const $ a' * y / (y+1)**2) a'}
    ComposeSigmoid a c e1 ->
      let AR gx _ (SUB sdsf1g beta2) _ gsens = analyzeExpr row e1
          b = gsens
          y = exp (a * (gx - c))
          z = y / (y + 1)
          a' = abs a
      in aR {fx = z,
             subf = SUB (const z) (a' * b),
             sdsf = SUB (\ beta -> a' * y / (y+1)**2 * sdsf1g (beta - a' * b)) (a' * b + beta2)}
    Tauoid a c i ->
      let x = row !! i
          y1 = exp ((-a) * (x - c))
          y2 = exp (a * (x - c))
          z = 2 / (y1 + y2)
          a' = abs a
      in aR {fx = z,
             subf = SUB (const z) a',
             sdsf = SUB (const $ a' * z) a'}
    ComposeTauoid a c e1 ->
      let AR gx _ (SUB sdsf1g beta2) _ gsens = analyzeExpr row e1
          b = gsens
          y1 = exp ((-a) * (gx - c))
          y2 = exp (a * (gx - c))
          z = 2 / (y1 + y2)
          a' = abs a
      in aR {fx = z,
             subf = SUB (const z) (a' * b),
             sdsf = SUB (\ beta -> a' * z * sdsf1g (beta - a' * b)) (a' * b + beta2)}
    PowerLN i r ->
      let x = row !! i
      in if x > 0
           then aR {fx = x ** r,
                    subf = SUB (const $ x ** r) (abs r),
                    sdsf = SUB (const $ abs r * x ** r) (abs r)}
           else error "analyzeExpr/PowerLN: condition (x > 0) not satisfied"
    Const c ->
      aR {fx = Q c,
          subf = SUB (const (Q $ abs c)) 0,
          sdsf = SUB (const (Q 0)) 0,
          gub = c,
          gsens = 0}
    ScaleNorm a e1 ->
      let AR fx1 (SUB subf1g subf1beta) (SUB sdsf1g sdsf1beta) gub gsens = analyzeExpr row e1
      in aR {fx = fx1,
             subf = SUB (\ beta -> subf1g (beta*a)) (subf1beta/a),
             sdsf = SUB (\ beta -> sdsf1g (beta*a) / a) (sdsf1beta/a),
             gub = gub,
             gsens = gsens/a}
    ZeroSens e1 ->
      let AR fx1 (SUB subf1g subf1beta) (SUB sdsf1g sdsf1beta) gub _ = analyzeExpr row e1
      in aR {fx = fx1,
             subf = SUB (const fx1) 0,
             sdsf = SUB (const (Q 0)) 0,
             gub = gub,
             gsens = 0}
    L p is ->
      let xs = map (row !!) is
          y = lpnorm p xs
      in aR {fx = y,
             subf = SUB (\ beta -> if y >= 1/beta then y else exp (beta * y - 1) / beta) 0,
             sdsf = SUB (const (Q 1)) 0,
             gsens = 1}
    LInf is ->
      let xs = map (row !!) is
          y = linfnorm xs
      in aR {fx = y,
             subf = SUB (\ beta -> if y >= 1/beta then y else exp (beta * y - 1) / beta) 0,
             sdsf = SUB (const (Q 1)) 0,
             gsens = 1}
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
      gubs = map gub ars
      gsenss = map gsens ars
      n = length ars
      c i beta = let s = ((sdsgs !! i) beta) in if s == 0 then Q 0 else s * product (map ($ beta) $ skipith i subgs)
      gc i = let s = (gsenss !! i) in if s == 0 then 0 else s * product (skipith i gubs)
  in aR {fx = product fxs,
         subf = SUB (\ beta -> product (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> linfnorm (map (\ i -> c i beta) [round 0..n P.- round 1])) (maximum (subfBetas ++ sdsfBetas)),
         gub = product gubs,
         gsens = B.linfnorm (map gc [round 0..n P.- round 1])}

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
  in aR {fx = product fxs,
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
  in aR {fx = minimum fxs,
         subf = SUB (\ beta -> minimum (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> maximum (map ($ beta) sdsgs)) (maximum sdsfBetas)}

combineArsMinT :: AnalysisResult -> AnalysisResult
combineArsMinT ar =
  aR {fx = minimumT (fx ar),
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
  in aR {fx = maximum fxs,
         subf = SUB (\ beta -> maximum (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> maximum (map ($ beta) sdsgs)) (maximum sdsfBetas)}

combineArsMaxT :: AnalysisResult -> AnalysisResult
combineArsMaxT ar =
  aR {fx = maximumT (fx ar),
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
      gsenss = map gsens ars
  in aR {fx = lpnorm p fxs,
         subf = SUB (\ beta -> lpnorm p (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> maximum (map ($ beta) sdsgs)) (maximum sdsfBetas),
         gsens = maximum gsenss}

combineArsLT :: Double -> AnalysisResult -> AnalysisResult
combineArsLT p ar =
  aR {fx = lpnormT p (fx ar),
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
      gsenss = map gsens ars
  in aR {fx = lpnorm p fxs,
         subf = SUB (\ beta -> lpnorm p (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> lpnorm 1 (map ($ beta) sdsgs)) (maximum sdsfBetas),
         gsens = B.lpnorm 1 gsenss}

combineArsLpInfT :: Double -> AnalysisResult -> AnalysisResult
combineArsLpInfT p ar =
  aR {fx = lpnormT p (fx ar),
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
      gsenss = map gsens ars
  in aR {fx = sum fxs,
         subf = SUB (\ beta -> sum (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> lqnorm p (map ($ beta) sdsgs)) (maximum sdsfBetas),
         gsens = B.lqnorm p gsenss}

combineArsSumpT :: Double -> AnalysisResult -> AnalysisResult
combineArsSumpT p ar =
  aR {fx = sumT (fx ar),
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
      gsenss = map gsens ars
  in aR {fx = sum fxs,
         subf = SUB (\ beta -> sum (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> lpnorm 1 (map ($ beta) sdsgs)) (maximum sdsfBetas),
         gsens = B.lpnorm 1 gsenss}

combineArsSumInfT :: AnalysisResult -> AnalysisResult
combineArsSumInfT ar =
  aR {fx = sumT (fx ar),
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
  in aR {fx = sum fxs,
         subf = SUB (\ beta -> sum (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> sum (map ($ beta) sdsgs)) (maximum sdsfBetas)}

analyzeTableExpr :: [String] -> String -> TableExpr -> AnalysisResult
analyzeTableExpr cols srt te =
  case te of
    SelectMin (expr : _) -> oneStepCombine combineArsMinT expr
    SelectMax (expr : _) -> oneStepCombine combineArsMaxT expr
    SelectL p (expr : _) -> twoStepCombine (combineArsLT p) (combineArsLpInfT p) expr
    SelectSump p (expr : _) -> twoStepCombine (combineArsSumpT p) combineArsSumInfT expr
    SelectSumInf (expr : _) -> oneStepCombine combineArsSumInfT expr
  where
    fixedArg arg expr arg' | arg' P.== arg = expr
    oneStepCombine combine expr =
      let
        AR fx _ (SUB sdsg subBeta) _ _ = combine (analyzeExprQ cols expr)
      in
        aR {fx = fx,
            sdsf = SUB (\ beta -> sdsg beta `Where` (srt ++ ".sensitive")) subBeta}
    twoStepCombine combine_p combine_inf expr =
      let
        AR fx _ (SUB sdsg subBeta) _ _ = combine_inf (analyzeExprQ cols expr)
        AR _ _ (SUB _ subBeta2) _ _ = combine_p $ AR {sdsf = SUB undefined subBeta}
      in aR {fx = fx,
             sdsf = SUB (\ beta ->
                           let
                             subquery = GroupBy ((sdsg beta `As` "sdsg") `Where` (srt ++ ".sensitive")) (srt ++ ".ID") ""
                             AR _ _ (SUB sdsg2 _) _ _ = combine_p $ AR {sdsf = SUB (fixedArg beta $ VarQ "sdsg") subBeta}
                             mainquery = sdsg2 beta
                           in
                             Subquery mainquery subquery)
                        subBeta2}

-- SELECT expr FROM fr WHERE wh
-- (colNames !! i) is the name of the variable with number i in expr
-- fr may contain multiple tables and aliases, e.g. "t as t1, t as t2, t3"
-- wh is the WHERE condition as a string, e.g. "t1.c1 = t2.c1 AND t1.c2 >= t2.c2"
-- srt is the name of the sensitive rows table
analyzeTableExprQ :: String -> String -> String -> [String] -> TableExpr -> AnalysisResult
analyzeTableExprQ fr wh srt colNames te =
  let AR fx1 (SUB subf1g subf1beta) (SUB sdsf1g sdsf1beta) gub gsens = analyzeTableExpr colNames srt te
  in AR (Select fx1 fr wh) (SUB ((\ x -> Select x fr wh) . subf1g) subf1beta) (SUB ((\ x -> Select x fr wh) . sdsf1g) sdsf1beta) gub gsens

performAnalyses :: ProgramOptions -> [String] -> [(String, TableExpr, String)] -> IO ()
performAnalyses args colNames tableExprData = do
  let debug = not (alternative args)
  let (tableNames,_,_) = unzip3 tableExprData
  let uniqueTableNames = nub tableNames
  when debug $ putStrLn "================================="
  when debug $ putStrLn "Generating SQL statements for creating input tables:\n"
  forM_ uniqueTableNames (\ t -> createTableSql t >>= putStr)
  when debug $ putStrLn "================================="
  when debug $ putStrLn "Generating SQL queries for computing the analysis results:"
  --let fromPart = intercalate ", " tableNames
  --let wherePart = ""
  forM_ tableExprData $ \ (tableName, te, sqlQuery) -> do
    let [_, fromWhere] = splitOn " FROM " sqlQuery
    let [fromPart, wherePart] = splitOn " WHERE " fromWhere
    when debug $ putStrLn ""
    when debug $ putStrLn "--------------------------------"
    when debug $ putStrLn $ "=== Analyzing table " ++ tableName ++ " ==="
    let ar = analyzeTableExprQ fromPart wherePart (sensRows tableName) colNames te
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
    when debug $ putStrLn (show qr ++ ";")
    let sds = subg (sdsf ar) beta
    when debug $ putStrLn "beta-smooth derivative sensitivity:"
    when debug $ putStrLn (show sds ++ ";")
