module Expr where

import Data.List
import Data.Map
import Debug.Trace
import qualified Data.Set as S

-- import Expr from Banach.hs
import qualified Banach as B
import Norms

-- let the variable names be alphanumeric strings starting with a character
type VarName = String

-----------------------------------------------------------------------------------
-- TODO: Expr and TableExpr are being synchronized with B.Expr and B.TableExpr

-- these are single-step Banach expressions, all 'Expr' and 'Var' substituted with 'VarName'
data Expr = Power VarName Double          -- x^r with norm | |, or E^r with norm N
          | PowerLN VarName Double        -- x^r with logarithmic norm: ||x|| = |ln x|, addition in Banach space is multiplication of real numbers
          | Exp Double VarName            -- e^(r*x) with norm | |
          | Sigmoid Double Double VarName -- s(a,c,x) = e^(a*(x-c))/(e^(a*(x-c)) + 1)
          | ScaleNorm Double VarName      -- E with norm a * N
          | ZeroSens VarName              -- E with sensitivity forced to zero (the same as ScaleNorm with a -> infinity)
          | L Double [VarName]            -- ||(x1,...,xn)||_p with l_q-norm where q = p/(p-1)
          | LInf [VarName]                -- same with p = infinity, q = 1
          | Prod [VarName]                -- E1*...*En with norm ||(N1,...,Nn)||_1 or N, where N is the common norm of all Ei
          | Min [VarName]                 -- min{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
          | Max [VarName]                 -- max{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
  deriving Show

-- expressions of type TableExpr use values from the whole table
-- the argument becomes a list when a query gets linked to a database
data TableExpr = SelectProd VarName        -- product (map E rows) with norm ||(N1,...,Nn)||_1 where Ni is N applied to ith row
               | SelectMin VarName         -- min (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]
               | SelectMax VarName         -- max (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]
               | SelectL Double VarName    -- ||(E1,...,En)||_p with norm ||(N1,...,Nn)||_p
               | SelectCount VarName       -- counts the rows, is rewritten to other expressions
               | Select VarName            -- does not apply aggregation, is used only for intermediate representation
  deriving Show

-- a function consists of unit expression assignments "Map VarName Expr" and returns a single "TableExpr"
-- an assigment is identitified by the assigned variable, we assume the variables are not reused
-- each assignment maps a variable to an expression
data Function
  = F (Map VarName Expr) TableExpr
  deriving (Show)

-- a small bit, denoting whether we are parsing a query or a norm
-- we define it, since a query and a norm have very similar format
data ParserInstance = QueryParsing | NormParsing

-----------------------------------------------------------------------------------
-- TODO: reconstruction of terms are being synchronized with B.Expr and B.TableExpr

extractArg :: TableExpr -> VarName
extractArg t =
    case t of
        SelectProd x -> x
        SelectMin x  -> x
        SelectMax x  -> x
        SelectL _ x  -> x
        Select x     -> x

queryArg :: TableExpr -> [B.Expr] -> Either [B.Expr] B.TableExpr
queryArg t ys =
    case t of
        SelectProd _ -> Right $ B.SelectProd ys
        SelectMin _  -> Right $ B.SelectMin ys
        SelectMax _  -> Right $ B.SelectMax ys
        SelectL c _  -> Right $ B.SelectL c ys
        Select _     -> Left  $ ys

normArg :: TableExpr -> ADouble
normArg t =
    case t of
        SelectProd _ -> Any
        SelectMin _  -> Any
        SelectMax _  -> Any
        SelectL c _  -> Exactly c
        Select _     -> (Exactly 0.0) -- this means that we do not compute the aggregate norm

-- Expr constructor variable arguments can be Var, Expr
-- we put all of them into one list and later check whether a variable is an input or an assignment variable
extractArgs :: Expr -> [VarName]
extractArgs t =
    case t of
        Power x _        -> [x]
        PowerLN x _      -> [x]
        Exp _ x          -> [x]
        Sigmoid _ _ x    -> [x]
        ScaleNorm _ x    -> [x]
        ZeroSens x       -> [x]
        L _ xs           -> xs
        LInf xs          -> xs
        Prod xs          -> xs
        Min xs           -> xs
        Max xs           -> xs

-- this is needed to make error of a missing head clearer
-- the errors come where the argument has to be an input variable, but it is actually an expression, and vice versa
headInputVar :: Expr -> [a] -> a
headInputVar t [] = error ("Cannot substitude variables into " ++ show t ++ ",\n the arguments are not of Var (input variable) type")
headInputVar t xs = head xs

headAsgnVar :: Expr -> [a] -> a
headAsgnVar t [] = error ("Cannot substitude variables into " ++ show t ++ ",\n the arguments are not of Expr (assignment variable) type")
headAsgnVar t xs = head xs

onlyInputVars :: Expr -> [a] -> [b] -> [a]
onlyInputVars t [] _ = error ("Cannot substitude variables into " ++ show t ++ ",\n the arguments are not of Var (input variable) type")
onlyInputVars t xs [] = xs
onlyInputVars t _ _ = error ("Cannot substitude variables into " ++ show t ++ ",\n some arguments are not of Var (input variable) type")

onlyAsgnVars :: Expr -> [a] -> [b] -> [b]
onlyAsgnVars t _ [] = error ("Cannot substitude variables into " ++ show t ++ ",\n the arguments are not of Expr (assignment variable) type")
onlyAsgnVars t [] xs = xs
onlyAsgnVars t _ _ = error ("Cannot substitude variables into " ++ show t ++ ",\n some arguments are not of Expr (assignment variable) type")

-- the constructor may depend on whether the arguments are input variables or expressions
-- arg1: the term
-- arg2: used input variables
-- arg3: used assignment variables
-- arg4: the list of input vars in turn used by asgn variables -- needed e.g to decide whether Prod becomes B.Prod or B.Prod2
queryExpression :: Expr -> [B.Var] -> [B.Expr] -> [S.Set B.Var] -> B.Expr
queryExpression t xs es vss =
    case t of
        Power _ c        -> if xs /= [] then
                                B.Power (headInputVar t xs) c
                            else
                                B.ComposePower (headAsgnVar t es) c
        PowerLN _ c      -> B.PowerLN (headInputVar t xs) c
        Exp c _          -> B.Exp c (headInputVar t xs)
        Sigmoid a c x    -> B.Sigmoid a c (headInputVar t xs)
        ScaleNorm c _    -> B.ScaleNorm c (headAsgnVar t es)
        ZeroSens _       -> B.ZeroSens (headAsgnVar t es)
        L c _            -> if xs /= [] then
                                B.L c (onlyInputVars t xs es)
                            else
                                B.ComposeL c (onlyAsgnVars t xs es)

        LInf _           -> B.LInf (onlyInputVars t xs es)
        Prod _           -> if (pairwiseDisjoint vss) then -- checks if the variables of different args are pairwise disjoint
                                B.Prod (onlyAsgnVars  t xs es)
                            else
                                B.Prod2 (onlyAsgnVars  t xs es)
        Min _            -> B.Min  (onlyAsgnVars  t xs es)
        Max _            -> B.Max  (onlyAsgnVars  t xs es)

-- the definition of Norm allows to use any variables inside argumets (both input and assignment variables)
normExpression :: Expr -> [a] -> [Norm a] -> [S.Set a] -> (Norm a)
normExpression t xs es _ =
    let zs = (Data.List.map (\ x -> Col x) xs) ++ es in
    case t of
        PowerLN _ _      -> NormLN (head zs)
        ScaleNorm c _    -> NormScale c (head zs)
        ZeroSens _       -> NormZero (head zs)
        L c _            -> NormL (Exactly c) zs
        LInf _           -> NormL Any zs

-- extracts all variables of the form "const:X" for a double X
extractConstants :: [Expr] -> [String]
extractConstants [] = []
extractConstants (t:ts) =
    let xs = extractArgs t in
    let xs' = Data.List.filter (\x -> if fst (splitAt 5 x) == "const" then True else False) xs in
    xs' ++ (extractConstants ts)

-----------------------------------------------
pairwiseDisjoint :: [S.Set B.Var] -> Bool
pairwiseDisjoint [] = True
pairwiseDisjoint (vs:vss) =
    let n = length $ Data.List.filter (\vs' -> not (S.null (S.intersection vs vs'))) vss in
    if (n == 0) then pairwiseDisjoint vss else False

