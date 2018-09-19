{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, RebindableSyntax, FlexibleInstances #-}

module BanachQ where

import Banach (Expr(..), TableExpr(..), (!!), chooseBeta, chooseBetaCustom, gamma, dualnorm, skipith)
import qualified Banach as B
import ProgramOptions
import CreateTablesQ
import DatabaseQ
import PolicyQ (VarState(..))
import RangeUtils

import qualified Prelude as P
import qualified Data.List as L
import Prelude hiding (fromInteger,fromRational,(!!),(+),(-),(*),(/),(**),(==),(/=),(<=),(>=),(<),(>),exp,abs,sum,product,minimum,maximum)
import Data.List hiding ((!!),sum,product,minimum,maximum)
import Data.List.Split
import qualified Data.Map as M
import Text.Printf
import Control.Monad
import System.Process
import qualified System.IO.Strict as StrictIO

sqlsaExecutablePathQuiet = "./sqlsa-quiet"
sqlsaExecutablePathVerbose = "./sqlsa-verbose"
combinedSensitivityTmpFileName = "_combined_sensitivity.tmp"

readTableToSensitivityMap :: IO (M.Map String Double)
readTableToSensitivityMap = do
  s <- StrictIO.readFile combinedSensitivityTmpFileName
  return $ M.fromList $ map ((\ [w1,w2] -> (w1, read w2 :: Double)) . words) $ lines s

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
               | BoolExprQ String          -- an SQL expression of boolean type

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

---------------- a simple constant propagation block
applyListFunQ :: String -> [ExprQ] -> ExprQ
applyListFunQ "greatest" [x] = x
applyListFunQ "greatest" xs =
  let ys = filter (\x -> case x of {Q _ -> True; _ -> False}) xs in
  case ys of
    [] -> ListFunQ "greatest" xs
    _  -> let zs = filter (\x -> case x of {Q _ -> False; _ -> True}) xs in
          let z  = Q $ maximum (map (\(Q c) -> c) ys) in
          case zs of
              [] -> z
              -- if z = 0 and all others are 'abs', then we may discard z
              _  -> case z of
                       Q 0 -> let ws = filter (\x -> case x of {FunQ "abs" _ -> True; _ -> False}) zs in
                              case compare (length zs) (length ws) of
                                  EQ -> case zs of
                                            [w] -> w
                                            _   -> ListFunQ "greatest" zs
                                  _  -> ListFunQ "greatest" (z:zs)
                       _   -> ListFunQ "greatest" (z:zs)

applyListFunQ "least" [x] = x
applyListFunQ "least" xs =
  let ys = filter (\x -> case x of {Q _ -> True; _ -> False}) xs in
  case ys of
    [] -> ListFunQ "least" xs
    _  -> let zs = filter (\x -> case x of {Q _ -> False; _ -> True}) xs in
          let z  = Q $ maximum (map (\(Q c) -> c) ys) in
          case zs of
              [] -> z
              -- if z = 0 and all others are 'abs', then we may discard zs
              _  -> case z of
                       Q 0 -> let ws = filter (\x -> case x of {FunQ "abs" _ -> True; _ -> False}) zs in
                              case compare (length zs) (length ws) of
                                  EQ -> z
                                  _  -> ListFunQ "least" (z:zs)
                       _   -> ListFunQ "least" (z:zs)

applyFunQ :: String -> ExprQ -> ExprQ
applyFunQ f x =
  case x of
    Q c -> case f of
              "exp" -> Q $ exp c
              "log" -> Q $ log c
              "abs" -> Q $ abs c
              _     -> FunQ f x
    _ -> FunQ f x

applyOpQ :: String -> ExprQ -> ExprQ -> ExprQ
applyOpQ op (Q cx) (Q cy) =
    case op of
        "+" -> Q (cx + cy)
        "-" -> Q (cx - cy)
        "*" -> Q (cx * cy)
        "/" -> Q (cx / cy)
        "^" -> Q (cx ** cy)

applyOpQ op x@(Q cx) y =
    case op of
        "+" -> if cx == 0 then y else (:+) x y
        "-" -> (:-) x y
        "*" -> if cx == 0 then Q 0 else (if cx == 1 then y else (:*) x y)
        "/" -> if cx == 0 then Q 0 else (:/) x y
        "^" -> if cx == 0 then Q 0 else (if cx == 1 then Q 1 else (:**) x y)

applyOpQ op x y@(Q cy) =
    case op of
        "+" -> if cy == 0 then x else (:+) x y
        "-" -> if cy == 0 then x else (:-) x y
        "*" -> if cy == 0 then Q 0 else (if cy == 1 then x else (:*) x y)
        "/" -> if cy == 0 then Q (1/0) else (if cy == 1 then x else (:/) x y)
        "^" -> if cy == 0 then Q 1 else (if cy == 1 then x else (:**) x y)

applyOpQ op x y =
    case op of
        "+" -> (:+) x y
        "-" -> (:-) x y
        "*" -> (:*) x y
        "/" -> (:/) x y
        "^" -> (:**) x y

constProp :: ExprQ -> ExprQ
constProp expr =
  case expr of
        Q c -> Q c
        VarQ x -> VarQ x
        FunQ f x -> applyFunQ f $ constProp x
        OpQ op x y -> OpQ op (constProp x) (constProp y)
        ListFunQ f xs -> applyListFunQ f $ map constProp xs

        IfThenElseQ (CmpOpQ op z1 z2) x y -> case z of
                                                   Just True  -> (constProp x)
                                                   Just False -> (constProp y)
                                                   Nothing    -> IfThenElseQ (CmpOpQ op nz1 nz2) (constProp x) (constProp y)
                                               where
                                                   nz1 = constProp z1
                                                   nz2 = constProp z2
                                                   z = constPropBool op nz1 nz2
        IfThenElseQ b x y -> IfThenElseQ b (constProp x) (constProp y)
        (x :+ y)  -> applyOpQ "+" (constProp x) (constProp y)
        (x :- y)  -> applyOpQ "-" (constProp x) (constProp y)
        (x :* y)  -> applyOpQ "*" (constProp x) (constProp y)
        (x :/ y)  -> applyOpQ "/" (constProp x) (constProp y)
        (x :** y) -> applyOpQ "^" (constProp x) (constProp y)
        Select x fr wh -> Select (constProp x) fr wh
        GroupBy x g h  -> GroupBy (constProp x) g h
        x `Where` y    -> (constProp x) `Where` y
        x `As` a       -> (constProp x) `As` a
        Subquery x y   -> Subquery (constProp x) (constProp y)

constPropBool :: String -> ExprQ -> ExprQ -> Maybe Bool
constPropBool op (Q cx) (Q cy) =
    case op of
        "="  -> if cx == cy then Just True else Just False
        "!=" -> if cx == cy then Just False else Just True
        "<=" -> if cx <= cy then Just True else Just False
        ">=" -> if cx >= cy then Just True else Just False
        "<"  -> if cx < cy  then Just True else Just False
        ">"  -> if cx > cy  then Just True else Just False

constPropBool op (Q cx) y =
    case op of
        ">=" -> if cx == infinity then Just True else Nothing
        _    -> Nothing

constPropBool op x (Q cy) =
    case op of
        "<=" -> if cy == infinity then Just True else Nothing
        _    -> Nothing

constPropBool _ _ _ = Nothing
----------------

instance Show ExprQ where
  show (Q x) | x >= 0    = if x == infinity then "99999.99" else show x
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
  show (BoolExprQ x) = '(' : x ++ ")"

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
  gsens :: Double,          -- (upper bound on) global sensitivity of the analyzed function, may be infinity
  arVarState :: VarState}   -- Range lb ub, if both lower and upper bound are known, otherwise Exact
  deriving Show

unknownSUB = SUB undefined (-1)

aR :: AnalysisResult
aR = AR {subf = unknownSUB, gub = infinity, gsens = infinity, arVarState = Exact}

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

getUbFromAr :: AnalysisResult -> Double
getUbFromAr ar = case arVarState ar of Range lb ub -> ub
                                       _           -> gub ar

getLbFromAr :: AnalysisResult -> Double
getLbFromAr ar = case arVarState ar of Range lb ub -> lb
                                       _           -> - gub ar

getRangeFromAr :: AnalysisResult -> VarState
getRangeFromAr ar = Range (getLbFromAr ar) (getUbFromAr ar)

analyzeExprQ :: [String] -> [VarState] -> Expr -> AnalysisResult
analyzeExprQ colNames = analyzeExpr (map VarQ colNames)

analyzeExpr :: [ExprQ] -> [VarState] -> Expr -> AnalysisResult
analyzeExpr row varStates = ae where
 ae expr =
  case expr of
    Prec (B.AR fx (B.SUB subg subBeta) (B.SUB sdsg sdsBeta)) -> AR {fx = Q fx, subf = SUB (Q . subg) subBeta, sdsf = SUB (Q . subg) subBeta,
                                                                    gub = if subBeta > 0 then infinity else subg 0,
                                                                    gsens = if sdsBeta > 0 then infinity else sdsg 0}
    -- we use this construction only for equality checks, so an UB on f itself is 1
    StringCond s ->
      aR {fx = VarQ s,
          subf = SUB (const (VarQ s)) 0,
          sdsf = SUB (const (Q 0)) 0,
          gub = 1.0,
          gsens = 0}
    Power i r ->
      let x = row !! i
          vs = varStates !! i
      in if r == 1
           then aR {fx = x,
                    subf = SUB (\ beta -> ifThenElse (abs x >= 1 / beta) (abs x) (exp (beta * abs x - 1) / beta)) 0,
                    sdsf = SUB (const (Q 1)) 0,
                    gub = getGubFromVs vs,
                    gsens = 1,
                    arVarState = vs}
           else if r >= 1
             then
               let x_ub = getUbFromVs vs
                   x_lb = max 0 (getLbFromVs vs)
                   ub = x_ub ** r
               in if x > 0
                   then aR {fx = x ** r,
                            subf = SUB (\ beta -> ifThenElse (x >= r/beta) (x ** r) (exp (beta*x - r) * (r/beta)**r)) 0,
                            sdsf = SUB (\ beta -> ifThenElse (x >= (r-1)/beta) (r * x**(r-1)) (r * exp (beta*x - (r-1)) * ((r-1)/beta)**(r-1))) 0,
                            gub = ub,
                            gsens = r * x_ub**(r-1),
                            arVarState = Range (x_lb ** r) ub}
                   else error "analyzeExpr/Power: condition (r >= 1 && x > 0 || r == 1) not satisfied"
             else error "analyzeExpr/Power: condition (r >= 1 && x > 0 || r == 1) not satisfied"
    ComposePower e1 r ->
      let ar @ (AR gx (SUB subf1g beta1) (SUB sdsf1g beta2) _ gsens _) = ae e1
          beta3 = (r-1)*beta1 + beta2
          b1 = if beta3 > 0 then beta1 / beta3 else 1/r
          b2 = if beta3 > 0 then beta2 / beta3 else 1/r
          gx_ub = getUbFromAr ar
          gx_lb = max 0 (getLbFromAr ar)
          ub = gx_ub ** r
      in if r >= 1
           then if gx > 0
                 then AR {fx = gx ** r,
                          subf = SUB (\ beta -> subf1g (beta / r) ** r) (r*beta1),
                          sdsf = SUB (\ beta -> r * (subf1g (b1 * beta))**(r-1) * sdsf1g (b2 * beta)) beta3,
                          gub = ub,
                          gsens = r * gx_ub ** (r-1) * gsens,
                          arVarState = Range (gx_lb ** r) ub}
                 else error "analyzeExpr/ComposePower: condition (r >= 1 && g(x) > 0) not satisfied"
           else error "analyzeExpr/ComposePower: condition (r >= 1 && g(x) > 0) not satisfied"
    Exp r i ->
      let x = row !! i
          x_ub = getUbFromVs (varStates !! i)
          x_lb = getLbFromVs (varStates !! i)
          f_x_ub = if r >= 0 then exp (r * x_ub) else exp (r * x_lb)
          f_x_lb = if r >= 0 then exp (r * x_lb) else exp (r * x_ub)
      in aR {fx = exp (r * x),
             subf = SUB (const $ exp (r * x)) (abs r),
             sdsf = SUB (const $ abs r * exp (r * x)) (abs r),
             gub = f_x_ub,
             gsens = abs r * f_x_ub,
             arVarState = Range f_x_lb f_x_ub}
    ComposeExp r e1 ->
      let ar @ (AR gx _ (SUB sdsf1g beta2) _ gsens _) = ae e1
          b = gsens
          gx_ub = getUbFromAr ar
          gx_lb = getLbFromAr ar
          f_x = exp (r * gx)
          f_x_ub = if r >= 0 then exp (r * gx_ub) else exp (r * gx_lb)
          f_x_lb = if r >= 0 then exp (r * gx_lb) else exp (r * gx_ub)
      in aR {fx = f_x,
             subf = SUB (const f_x) (abs r * b),
             sdsf = SUB (\ beta -> abs r * f_x * sdsf1g (beta - abs r * b)) (abs r * b + beta2),
             gub = f_x_ub,
             gsens = abs r * f_x_ub * gsens,
             arVarState = Range f_x_lb f_x_ub}
    Sigmoid a c i ->
      let x = row !! i
          vs = varStates !! i
          y = exp (a * (x - c))
          z = y / (y + 1)
          a' = abs a
          ub = case vs of Range lb ub -> let x = ub
                                             y = exp (a * (x - c))
                                             z = y / (y + 1)
                                         in z
                          _ -> infinity
      in aR {fx = z,
             subf = SUB (const z) a',
             sdsf = SUB (const $ a' * y / (y+1)**2) a',
             gub = ub,
             gsens = a'/4,
             arVarState = Range 0 ub}
    ComposeSigmoid a c e1 ->
      let ar @ (AR gx _ (SUB sdsf1g beta2) _ gsens _) = ae e1
          b = gsens
          y = exp (a * (gx - c))
          z = y / (y + 1)
          a' = abs a
          gx_ub = getUbFromAr ar
          ub = if isInfinite gx_ub then infinity else let gx = gx_ub
                                                          y = exp (a * (gx - c))
                                                          z = y / (y + 1)
                                                      in z
      in aR {fx = z,
             subf = SUB (const z) (a' * b),
             sdsf = SUB (\ beta -> a' * y / (y+1)**2 * sdsf1g (beta - a' * b)) (a' * b + beta2),
             gub = ub,
             gsens = a'/4 * gsens,
             arVarState = Range 0 ub}
    -- 'aa' is the actual sigmoid precision, 'ab' is the smoothness that we want
    SigmoidPrecise aa ab c i ->
      let x = row !! i
          vs = varStates !! i
          y = exp (ab * (x - c))
          y' = exp (aa * (x - c))
          z  = y' / (y'+1)
          a' = abs ab
          x_ub = getUbFromVs vs
          ub = case vs of Range lb ub -> let x = x_ub
                                             y' = exp (aa * (x - c))
                                             z  = y' / (y'+1)
                                         in z
                          _ -> infinity
      in aR {fx = z,
             subf = SUB (const (Q 1)) 0,
             sdsf = SUB (const $ aa * y / (y+1)**2) a',
             gub = ub,
             gsens = abs aa / 4,
             arVarState = Range 0 ub}
    ComposeSigmoidPrecise aa ab c e1 ->
      let ar @ (AR gx _ (SUB sdsf1g beta2) _ gsens _) = ae e1
          b = gsens
          y = exp (ab * (gx - c))
          y' = exp (aa * (gx - c))
          z = y' / (y' + 1)
          a' = abs ab
          gx_ub = getUbFromAr ar
          ub = if isInfinite gx_ub then infinity else let gx = gx_ub
                                                          y' = exp (aa * (gx - c))
                                                          z = y' / (y' + 1)
                                                      in z
      in aR {fx = z,
             subf = SUB (const (Q 1)) 0,
             sdsf = SUB (\ beta -> aa * y / (y+1)**2 * sdsf1g (beta - a' * b)) (a' * b + beta2),
             gub = ub,
             gsens = abs aa / 4 * gsens,
             arVarState = Range 0 ub}
    Tauoid a c i ->
      let x = row !! i
          y1 = exp ((-a) * (x - c))
          y2 = exp (a * (x - c))
          z = 2 / (y1 + y2)
          a' = abs a
      in aR {fx = z,
             subf = SUB (const z) a',
             sdsf = SUB (const $ a' * z) a',
             gub = 1,
             gsens = a',
             arVarState = Range 0 1}
    ComposeTauoid a c e1 ->
      let AR gx _ (SUB sdsf1g beta2) _ gsens _ = ae e1
          b = gsens
          y1 = exp ((-a) * (gx - c))
          y2 = exp (a * (gx - c))
          z = 2 / (y1 + y2)
          a' = abs a
      in aR {fx = z,
             subf = SUB (const z) (a' * b),
             sdsf = SUB (\ beta -> a' * z * sdsf1g (beta - a' * b)) (a' * b + beta2),
             gub = 1,
             gsens = a' * gsens,
             arVarState = Range 0 1}

    TauoidPrecise aa ab c i ->
      let x = row !! i
          y1 = exp ((-ab) * (x - c))
          y2 = exp (ab * (x - c))
          y1' = exp ((-aa) * (x - c))
          y2' = exp (aa * (x - c))
          z = 2 / (y1' + y2')
          a' = abs ab
      in aR {fx = z,
             subf = SUB (const (Q 1)) 0,
             sdsf = SUB (const $ aa * 2 / (y1 + y2)) a',
             gub = 1,
             gsens = abs aa,
             arVarState = Range 0 1}
    ComposeTauoidPrecise aa ab c e1 ->
      let AR gx _ (SUB sdsf1g beta2) _ gsens _ = ae e1
          b = gsens
          y1 = exp ((-ab) * (gx - c))
          y2 = exp (ab * (gx - c))
          y1' = exp ((-aa) * (gx - c))
          y2' = exp (aa * (gx - c))
          z = 2 / (y1' + y2')
          a' = abs ab
      in aR {fx = z,
             subf = SUB (const (Q 1)) 0,
             sdsf = SUB (\ beta -> aa * 2 / (y1 + y2) * sdsf1g (beta - a' * b)) (a' * b + beta2),
             gub = 1,
             gsens = abs aa * gsens,
             arVarState = Range 0 1}

    L0Predicate i p ->
      let VarQ x = row !! i
      in aR {fx = if BoolExprQ (p x) then Q 1 else Q 0,
             subf = SUB (\ beta -> if BoolExprQ (p x) then Q 1 else Q (exp (-beta))) 0,
             sdsf = SUB (const (Q 1)) 0,
             gub = 1,
             gsens = 1,
             arVarState = Range 0 1}
    PowerLN i r ->
      let x = row !! i
          x_ub = getUbFromVs (varStates !! i)
          x_lb = getLbFromVs (varStates !! i)
          y_ub = if r >= 0 then x_ub ** r else if x_lb > 0 then x_lb ** r else infinity
          y_lb = if r >= 0 then (if x_lb > 0 then x_lb ** r else 0) else x_ub ** r
      in if x > 0
           then aR {fx = x ** r,
                    subf = SUB (const $ x ** r) (abs r),
                    sdsf = SUB (const $ abs r * x ** r) (abs r),
                    gub = y_ub,
                    gsens = if r >= 0 then r * x_ub ** r else if x_lb > 0 then abs r * x_lb ** r else infinity,
                    arVarState = Range y_lb y_ub}
           else error "analyzeExpr/PowerLN: condition (x > 0) not satisfied"
    Const c ->
      aR {fx = Q c,
          subf = SUB (const (Q $ abs c)) 0,
          sdsf = SUB (const (Q 0)) 0,
          gub = abs c,
          gsens = 0,
          arVarState = Range c c}
    ScaleNorm a e1 ->
      let AR fx1 (SUB subf1g subf1beta) (SUB sdsf1g sdsf1beta) gub gsens vs = ae e1
      in aR {fx = fx1,
             subf = SUB (\ beta -> subf1g (beta*a)) (subf1beta/a),
             sdsf = SUB (\ beta -> sdsf1g (beta*a) / a) (sdsf1beta/a),
             gub = gub,
             gsens = gsens/a,
             arVarState = vs}
    ZeroSens e1 ->
      let AR fx1 (SUB subf1g subf1beta) (SUB sdsf1g sdsf1beta) gub _ vs = ae e1
      in aR {fx = fx1,
             subf = SUB (const fx1) 0,
             sdsf = SUB (const (Q 0)) 0,
             gub = gub,
             gsens = 0,
             arVarState = vs}
    L p is ->
      let xs = map (row !!) is
          y = lpnorm p xs
          vs = rangeLpNorm p $ map (getRangeFromVs . (varStates !!)) is
      in aR {fx = y,
             subf = SUB (\ beta -> if y >= 1/beta then y else exp (beta * y - 1) / beta) 0,
             sdsf = SUB (const (Q 1)) 0,
             gub = getGubFromVs vs,
             gsens = 1,
             arVarState = vs}
    LInf is ->
      let xs = map (row !!) is
          y = linfnorm xs
          vs = rangeLInfNorm $ map (getRangeFromVs . (varStates !!)) is
      in aR {fx = y,
             subf = SUB (\ beta -> if y >= 1/beta then y else exp (beta * y - 1) / beta) 0,
             sdsf = SUB (const (Q 1)) 0,
             gub = getGubFromVs vs,
             gsens = 1,
             arVarState = vs}
    Prod es -> combineArsProd $ map ae es
    Prod2 es -> combineArsProd2 $ map ae es
    Min es -> combineArsMin $ map ae es
    Max es -> combineArsMax $ map ae es
    ComposeL p es -> combineArsL p $ map ae es
    Sump p es -> combineArsSump p $ map ae es
    SumInf es -> combineArsSumInf $ map ae es
    Sum2 es -> combineArsSum2 $ map ae es

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
      rs = map getRangeFromAr ars
      n = length ars
      c i beta = let s = ((sdsgs !! i) beta) in if s == 0 then Q 0 else s * product (map ($ beta) $ skipith i subgs)
      gc i = let s = (gsenss !! i) in if s == 0 then 0 else s * product (skipith i gubs)
  in aR {fx = product fxs,
         subf = SUB (\ beta -> product (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> linfnorm (map (\ i -> c i beta) [round 0..n P.- round 1])) (maximum (subfBetas ++ sdsfBetas)),
         gub = product gubs,
         gsens = B.linfnorm (map gc [round 0..n P.- round 1]),
         arVarState = rangeProduct rs}

combineArsProd2 :: [AnalysisResult] -> AnalysisResult
combineArsProd2 ars =
  let fxs = map fx ars
      subfs = map subf ars
      sdsfs = map sdsf ars
      subfBetas = map subBeta subfs
      sdsfBetas = map subBeta sdsfs
      subgs = map subg subfs
      sdsgs = map subg sdsfs
      gubs = map gub ars
      gsenss = map gsens ars
      rs = map getRangeFromAr ars
      n = length ars
      divByn :: Double -> Double
      divByn x = x / (fromIntegral n :: Double)
      c i beta = ((sdsgs !! i) (divByn beta)) * product (map ($ (divByn beta)) $ skipith i subgs)
      gc i = let s = (gsenss !! i) in if s == 0 then 0 else s * product (skipith i gubs)
  in aR {fx = product fxs,
         subf = SUB (\ beta -> product (map ($ (divByn beta)) subgs)) (sum subfBetas),
         sdsf = SUB (\ beta -> sum (map (\ i -> c i beta) [round 0..n P.- round 1])) (sum subfBetas + maximum (zipWith (-) sdsfBetas subfBetas)),
         gub = product gubs,
         gsens = sum (map gc [round 0..n P.- round 1]),
         arVarState = rangeProduct rs}

combineArsMin :: [AnalysisResult] -> AnalysisResult
combineArsMin ars =
  let fxs = map fx ars
      subfs = map subf ars
      sdsfs = map sdsf ars
      subfBetas = map subBeta subfs
      sdsfBetas = map subBeta sdsfs
      subgs = map subg subfs
      sdsgs = map subg sdsfs
      gsenss = map gsens ars
      lbs = map getLbFromAr ars
      ubs = map getUbFromAr ars
      vs = Range (minimum lbs) (minimum ubs)
  in aR {fx = minimum fxs,
         subf = SUB (\ beta -> minimum (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> maximum (map ($ beta) sdsgs)) (maximum sdsfBetas),
         gub = getGubFromVs vs,
         gsens = maximum gsenss,
         arVarState = vs}

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
      gubs = map gub ars
      gsenss = map gsens ars
      lbs = map getLbFromAr ars
      ubs = map getUbFromAr ars
      vs = Range (maximum lbs) (maximum ubs)
  in aR {fx = maximum fxs,
         subf = SUB (\ beta -> maximum (map ($ beta) subgs)) (maximum subfBetas),
         sdsf = SUB (\ beta -> maximum (map ($ beta) sdsgs)) (maximum sdsfBetas),
         gub = getGubFromVs vs,
         gsens = maximum gsenss,
         arVarState = vs}

combineArsMaxT :: AnalysisResult -> AnalysisResult
combineArsMaxT ar =
  aR {fx = maximumT (fx ar),
      subf = SUB (\ beta -> maximumT (subg (subf ar) beta)) (subBeta (subf ar)),
      sdsf = SUB (\ beta -> maximumT (subg (sdsf ar) beta)) (subBeta (sdsf ar))}

combineArsLp :: Double -> [AnalysisResult] -> AnalysisResult
combineArsLp p ars =
  let fxs = map fx ars
      subfs = map subf ars
      subfBetas = map subBeta subfs
      subgs = map subg subfs
      vs = rangeLpNorm p $ map getRangeFromAr ars
  in aR {fx = lpnorm p fxs,
         subf = SUB (\ beta -> lpnorm p (map ($ beta) subgs)) (maximum subfBetas),
         gub = getUbFromVs vs,
         arVarState = vs}

combineArsL :: Double -> [AnalysisResult] -> AnalysisResult
combineArsL p ars =
  let sdsfs = map sdsf ars
      sdsfBetas = map subBeta sdsfs
      sdsgs = map subg sdsfs
      gsenss = map gsens ars
  in (combineArsLp p ars) {
         sdsf = SUB (\ beta -> maximum (map ($ beta) sdsgs)) (maximum sdsfBetas),
         gsens = maximum gsenss}

-- the computed function is l_p-norm but the norm is l_infinity
combineArsLpInf :: Double -> [AnalysisResult] -> AnalysisResult
combineArsLpInf p ars =
  let sdsfs = map sdsf ars
      sdsfBetas = map subBeta sdsfs
      sdsgs = map subg sdsfs
      gsenss = map gsens ars
  in (combineArsLp p ars) {
         sdsf = SUB (\ beta -> lpnorm 1 (map ($ beta) sdsgs)) (maximum sdsfBetas),
         gsens = B.lpnorm 1 gsenss}

combineArsLpT :: Double -> AnalysisResult -> AnalysisResult
combineArsLpT p ar =
  aR {fx = lpnormT p (fx ar),
      subf = SUB (\ beta -> lpnormT p (subg (subf ar) beta)) (subBeta (subf ar)),
      gub = if p == 1 then gub ar else infinity,
      gsens = if p == 1 then gsens ar else infinity}

combineArsLT :: Double -> AnalysisResult -> AnalysisResult
combineArsLT p ar = (combineArsLpT p ar) {sdsf = SUB (\ beta -> maximumT (subg (sdsf ar) beta)) (subBeta (sdsf ar))}

combineArsLpInfT :: Double -> AnalysisResult -> AnalysisResult
combineArsLpInfT p ar = (combineArsLpT p ar) {sdsf = SUB (\ beta -> lpnormT 1 (subg (sdsf ar) beta)) (subBeta (sdsf ar))}

combineArsSum :: [AnalysisResult] -> AnalysisResult
combineArsSum ars =
  let fxs = map fx ars
      subfs = map subf ars
      subfBetas = map subBeta subfs
      subgs = map subg subfs
      gubs = map gub ars
      lbs = map getLbFromAr ars
      ubs = map getUbFromAr ars
      vs = Range (sum lbs) (sum ubs)
  in aR {fx = sum fxs,
         subf = SUB (\ beta -> sum (map ($ beta) subgs)) (maximum subfBetas),
         gub = getGubFromVs vs,
         arVarState = vs}

combineArsSump :: Double -> [AnalysisResult] -> AnalysisResult
combineArsSump p ars =
  let sdsfs = map sdsf ars
      sdsfBetas = map subBeta sdsfs
      sdsgs = map subg sdsfs
      gsenss = map gsens ars
  in (combineArsSum ars) {
         sdsf = SUB (\ beta -> lqnorm p (map ($ beta) sdsgs)) (maximum sdsfBetas),
         gsens = B.lqnorm p gsenss}

combineArsSumInf :: [AnalysisResult] -> AnalysisResult
combineArsSumInf ars =
  let sdsfs = map sdsf ars
      sdsfBetas = map subBeta sdsfs
      sdsgs = map subg sdsfs
      gsenss = map gsens ars
  in (combineArsSum ars) {
         sdsf = SUB (\ beta -> lpnorm 1 (map ($ beta) sdsgs)) (maximum sdsfBetas),
         gsens = B.lpnorm 1 gsenss}

combineArsSum2 :: [AnalysisResult] -> AnalysisResult
combineArsSum2 ars =
  let sdsfs = map sdsf ars
      sdsfBetas = map subBeta sdsfs
      sdsgs = map subg sdsfs
      gsenss = map gsens ars
  in (combineArsSum ars) {
         sdsf = SUB (\ beta -> sum (map ($ beta) sdsgs)) (maximum sdsfBetas),
         gsens = sum gsenss}

combineArsSumT :: AnalysisResult -> AnalysisResult
combineArsSumT ar =
  aR {fx = sumT (fx ar),
      subf = SUB (\ beta -> sumT (subg (subf ar) beta)) (subBeta (subf ar)),
      gub = gub ar,
      gsens = gsens ar}

combineArsSumpT :: Double -> AnalysisResult -> AnalysisResult
combineArsSumpT p ar =
  (combineArsSumT ar) {sdsf = SUB (\ beta -> lqnormT p (subg (sdsf ar) beta)) (subBeta (sdsf ar))}

combineArsSumInfT :: AnalysisResult -> AnalysisResult
combineArsSumInfT ar =
  (combineArsSumT ar) {sdsf = SUB (\ beta -> lpnormT 1 (subg (sdsf ar) beta)) (subBeta (sdsf ar))}

analyzeTableExpr :: [String] -> [VarState] -> String -> TableExpr -> AnalysisResult
analyzeTableExpr cols varStates srt te =
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
        AR fx _ (SUB sdsg subBeta) gub gsens _ = combine (analyzeExprQ cols varStates expr)
      in
        aR {fx = fx,
            sdsf = SUB (\ beta -> sdsg beta `Where` (srt ++ ".sensitive")) subBeta,
            gub = gub,
            gsens = gsens}
    twoStepCombine combine_p combine_inf expr =
      let
        AR fx _ (SUB sdsg subBeta) gub gsens _ = combine_inf (analyzeExprQ cols varStates expr)
        AR _ _ (SUB _ subBeta2) _ _ _ = combine_p $ AR {sdsf = SUB undefined subBeta}
      in aR {fx = fx,
             sdsf = SUB (\ beta ->
                           let
                             subquery = GroupBy ((sdsg beta `As` "sdsg") `Where` (srt ++ ".sensitive")) (srt ++ ".ID") ""
                             AR _ _ (SUB sdsg2 _) _ _ _ = combine_p $ AR {sdsf = SUB (fixedArg beta $ VarQ "sdsg") subBeta}
                             mainquery = sdsg2 beta
                           in
                             Subquery mainquery subquery)
                        subBeta2,
             gub = gub,
             gsens = gsens}

-- SELECT expr FROM fr WHERE wh
-- (colNames !! i) is the name of the variable with number i in expr
-- fr may contain multiple tables and aliases, e.g. "t as t1, t as t2, t3"
-- wh is the WHERE condition as a string, e.g. "t1.c1 = t2.c1 AND t1.c2 >= t2.c2"
-- srt is the name of the sensitive rows table
analyzeTableExprQ :: String -> String -> String -> [String] -> [VarState] -> TableExpr -> AnalysisResult
analyzeTableExprQ fr wh srt colNames varStates te =
  let AR fx1 (SUB subf1g subf1beta) (SUB sdsf1g sdsf1beta) gub gsens vs = analyzeTableExpr colNames varStates srt te
  in AR (Select fx1 fr wh) (SUB ((\ x -> Select x fr wh) . subf1g) subf1beta) (SUB ((\ x -> Select x fr wh) . sdsf1g) sdsf1beta) gub gsens vs

performAnalyses :: ProgramOptions -> Double -> Maybe Double -> String -> String -> String -> [String] -> [(String,[(String, String)])] -> [(String,[Int],Bool)] -> [String] -> [(String, TableExpr, (String,String,String))] -> M.Map String VarState -> IO (Double,[(String, [(String, (Double, Double))])])
performAnalyses args epsilon beta dataPath separator initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap = do

  let debug = not (alternative args)
  let (tableNames,_,_) = unzip3 tableExprData
  let uniqueTableNames = nub tableNames
  when debug $ putStrLn "================================="
  when debug $ putStrLn "Generating SQL statements for creating input tables:\n"
  let policy = (policyAnalysis args)
  ctss <- if (not (dbCreateTables args)) then (do return []) else
                  forM uniqueTableNames $ \ t -> do cts <- createTableSqlTyped policy dataPath separator t typeMap
                                                    when debug $ putStr (concatMap (++ ";\n") cts)
                                                    return cts

  when (dbCreateTables args) $ sendQueriesToDbAndCommit args (concat ctss)
  when debug $ putStrLn "================================="
  when debug $ putStrLn "Computing the initial query:"
  when debug $ putStrLn initialQuery
  qr <- if (dbSensitivity args) then sendDoubleQueryToDb args initialQuery else (do return 0)
  when (dbSensitivity args && debug) $ putStrLn (show qr)
  when debug $ putStrLn "================================="
  when debug $ putStrLn "Generating SQL queries for computing the analysis results:"
  --let fromPart = intercalate ", " tableNames
  --let wherePart = ""
  --forM_ tableExprData $ \ (tableName, te, sqlQuery) -> do
  --  let [_, fromWhere] = splitOn " FROM " sqlQuery
  --  let [fromPart, wherePart] = splitOn " WHERE " fromWhere
  let varStates = map (M.findWithDefault Exact `flip` attMap) colNames
  when debug $ printf "colNames = %s\n" (show colNames)
  when debug $ printf "varStates = %s\n" (show varStates)
  res00 <- forM tableExprData $ \ (tableName, te, (_,fromPart,wherePart)) -> do
    when debug $ putStrLn ""
    when debug $ putStrLn "--------------------------------"
    when debug $ putStrLn $ "\\echo === Analyzing table " ++ tableName ++ " ==="
    when debug $ print te
    result <- performAnalysis args epsilon beta fromPart wherePart tableName colNames varStates sensitiveVarList te
    return (tableName, result)

  when (combinedSens args) $ when debug $ putStrLn "\n-----------------\nCombined sensitivities:"
  res0 <- forM res00 $ \ (tableName, (b,sds,combinedRes)) -> do
    when (combinedSens args) $ when debug $ putStr combinedRes
    return (tableName,(b,sds))

  let taskAggr0 = map (\(taskName,is,b) -> (taskName, B.sumGroupsWith (foldr (\(x1,y1) (x2,y2) -> (max x1 x2, y1 + y2)) (0,0)) $ map (res0 !!) is, b)) taskMap

  -- add an aggregated result to the output, sum up the sensitivities and take time minimal b
  let taskAggr = map (\(taskName,vs,b) ->
                         if b then
                             let v = foldr (\(x1,y1) (x2,y2) -> (max x1 x2, y1 + y2)) (0,0) (snd $ unzip vs) in
                             (taskName, (B.resultForAllTables, v):vs)
                         else
                             (taskName,vs)
                     ) taskAggr0
  return (qr,taskAggr)


performAnalysis :: ProgramOptions -> Double -> Maybe Double -> String -> String -> String -> [String] -> [VarState] -> [String] -> TableExpr -> IO (Double,Double,String)
performAnalysis args epsilon fixedBeta fromPart wherePart tableName colNames varStates sensitiveVarList te = do
    let debug = not (alternative args)
    -- TODO this is a hack, we will do it in the other way, so that it will be no longer needed
    let policy = (policyAnalysis args)
    let ar = analyzeTableExprQ fromPart wherePart (sensRows (if policy then takeWhile (\x -> case x of {'#' -> False; _ -> True}) tableName else tableName)) colNames varStates te
    when debug $putStrLn "Analysis result:"
    when debug $print ar
    --let epsilon = getEpsilon args
    when debug $ printf "epsilon = %0.6f\n" epsilon
    when debug $ printf "gamma = %0.6f\n" gamma
    let defaultBeta = epsilon / (2 * (gamma + 1))
    --let fixedBeta = getBeta args
    let beta = chooseSUBBeta defaultBeta fixedBeta (sdsf ar)
    when debug $ printf "beta = %0.6f\n" beta
    let b = epsilon / (gamma + 1) - beta
    when debug $ printf "b = %0.6f\n" b
    let qr = constProp $ fx ar
    when debug $ putStrLn "Query result:"
    when debug $ putStrLn (show qr ++ ";")
    when (dbSensitivity args && debug) $ sendDoubleQueryToDb args (show qr) >>= printf "database returns %0.6f\n"
    let sds = constProp $ subg (sdsf ar) beta
    when debug $ putStrLn "-- beta-smooth derivative sensitivity:"
    when debug $ putStrLn (show sds ++ ";")
    sds_value <- if (dbSensitivity args) then sendDoubleQueryToDb args (show sds) else (do return 0)
    when (dbSensitivity args && debug) $ printf "database returns %0.6f\n" sds_value
    (combinedSens_value,combinedRes) <- if combinedSens args
      then do
        --let sqlsaExecutablePath = if debug then sqlsaExecutablePathQuiet else sqlsaExecutablePathVerbose
        let sqlsaExecutablePath = sqlsaExecutablePathQuiet
        when debug $ printf "%s --combined-sens%s -B %f -S %f %s %s\n" sqlsaExecutablePath (if null sensitiveVarList then "" else " -f " ++ intercalate "," sensitiveVarList) beta (gub ar) (inputFp1 args) (inputFp2 args)
        let sqlsaArgs = ("--combined-sens" :
                         (if null sensitiveVarList then id else ("-f" :) . (intercalate "," sensitiveVarList :))
                         ["-B", show beta, "-S", show (gub ar), inputFp1 args, inputFp2 args])
        callProcess sqlsaExecutablePath sqlsaArgs
        localSensMap <- readTableToSensitivityMap
        callProcess sqlsaExecutablePath ("--count-query" : sqlsaArgs)
        localCountSensMap <- readTableToSensitivityMap
        when debug $ printf "localSensMap = %s\n" (show localSensMap)
        when debug $ printf "localCountSensMap = %s\n" (show localCountSensMap)
        let localSens = localSensMap M.! tableName
        let localCountSens = localCountSensMap M.! tableName
        let Just distanceG = getG args
        let ls = localSens / distanceG -- local sensitivity scaled to the combined distance
        let gsb = localCountSens * gsens ar / exp (beta * distanceG)
        let combinedSens = maximum [ls, sds_value, gsb]
        let res = printf "table=%s gub=%0.6f gsens=%0.6f localSens=%0.6f localCountSens=%0.6f ls=%0.6f sds=%0.6f gsb=%0.6f combinedSens=%0.6f\n"
                         tableName (gub ar) (gsens ar) localSens localCountSens ls sds_value gsb combinedSens
        when debug $ putStr res
        return (combinedSens,res)
      else
        return (sds_value,"")
    return (b,combinedSens_value,combinedRes)
    --return (b,sds_value,combinedRes)

