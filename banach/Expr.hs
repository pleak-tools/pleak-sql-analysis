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
          | Const Double                  -- constant c (real number, may be negative) in a zero-dimensional Banach space (with trivial norm)
          | ScaleNorm Double VarName      -- E with norm a * N
          | ZeroSens VarName              -- E with sensitivity forced to zero (the same as ScaleNorm with a -> infinity)
          | L Double [VarName]            -- ||(x1,...,xn)||_p with l_q-norm where q = p/(p-1)
          | LInf [VarName]                -- same with p = infinity, q = 1
          | Prod [VarName]                -- E1*...*En with norm that is not specified yet and will be derived later
          | Min [VarName]                 -- min{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
          | Max [VarName]                 -- max{E1,...,En} with norm ||(N1,...,Nn)||_p, p is arbitrary in [1,infinity]
          | Sump Double [VarName]         -- E1+...+En with norm ||(N1,...,Nn)||_p
          | SumInf [VarName]              -- E1+...+En with norm ||(N1,...,Nn)||_infinity
          | Sum [VarName]                 -- E1+...+En with norm that is not specified yet and will be derived later
          | Id VarName                    -- identity function, used for input table values
  deriving Show

-- expressions of type TableExpr use values from the whole table
-- the argument becomes a list when a query gets linked to a database
data TableExpr = SelectProd VarName        -- product (map E rows) with norm ||(N1,...,Nn)||_1 where Ni is N applied to ith row
               | SelectMin VarName         -- min (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]
               | SelectMax VarName         -- max (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]
               | SelectL Double VarName    -- ||(E1,...,En)||_p with norm ||(N1,...,Nn)||_p
               | SelectSump Double VarName -- E1+...+En with norm ||(N1,...,Nn)||_p
               | SelectSumInf VarName      -- E1+...+En with norm ||(N1,...,Nn)||_infinity
               | SelectSum VarName         -- E1+...+En with norm that is not specified yet and will be derived later
               | SelectCount VarName       -- counts the rows, is rewritten to other expressions
               | Select VarName            -- does not apply aggregation, is used only for intermediate representation
               | Filt Ordering VarName Double  -- used for filters, actually is not a "Table" expression, we just use the same data structure
  deriving Show

-----------------------------------------------------------------------------------
-- TODO: reconstruction of terms is being synchronized with B.Expr and B.TableExpr

extractArg :: TableExpr -> VarName
extractArg t =
    case t of
        SelectCount x  -> x
        SelectProd x   -> x
        SelectMin x    -> x
        SelectMax x    -> x
        SelectL _ x    -> x
        SelectSump _ x -> x
        SelectSumInf x -> x
        SelectSum  x   -> x
        Select x       -> x
        Filt _ x _   -> x

queryArg :: TableExpr -> [B.Expr] -> B.TableExpr
queryArg t ys =
    case t of
        SelectProd _   -> B.SelectProd ys
        SelectMin _    -> B.SelectMin ys
        SelectMax _    -> B.SelectMax ys
        SelectL c _    -> B.SelectL c ys
        SelectSump c _ -> B.SelectSump c ys
        SelectSumInf _ -> B.SelectSumInf ys
        -- let it be Sump 1.0 by default, we can take a coarser norm later if necessary
        SelectSum  _   -> B.SelectSump 1.0 ys
        -- if it turns out that SelectCount is left as it is,
        -- then all filters are defined over non-sensitive variables, so there are no privacy issues
        SelectCount _  -> B.SelectSump 1.0 (Data.List.map (\_ -> B.ZeroSens (B.Const 1.0)) ys)

normArg :: TableExpr -> ADouble
normArg t =
    case t of
        SelectMax _  -> Any
        SelectL c _  -> Exactly c

-- Expr constructor variable arguments can be Var, Expr
-- we put all of them into one list and later check whether a variable is an input or an assignment variable
extractArgs :: Expr -> [VarName]
extractArgs t =
    case t of
        Power x _        -> [x]
        PowerLN x _      -> [x]
        Exp _ x          -> [x]
        Sigmoid _ _ x    -> [x]
        Const _          -> []
        ScaleNorm _ x    -> [x]
        ZeroSens x       -> [x]
        L _ xs           -> xs
        LInf xs          -> xs
        Prod xs          -> xs
        Min xs           -> xs
        Max xs           -> xs
        Sump _ xs        -> xs
        SumInf xs        -> xs
        Sum xs           -> xs
        Id  x            -> [x]

-- this is needed to make error of a missing head clearer
-- the errors come where the argument has to be an input variable, but it is actually an expression, and vice versa
headInputVar :: Expr -> [a] -> a
headInputVar t [] = error ("Cannot substitude variables into " ++ show t ++ ",\n the arguments are not of Var (input variable) type")
headInputVar t xs = head xs

headAsgnVar :: Expr -> [a] -> a
headAsgnVar t [] = error ("Cannot substitude variables into " ++ show t ++ ",\n the arguments are not of Expr (assignment variable) type")
headAsgnVar t xs = head xs

-- if some variables are not immediate inputs, they may just be represented as (B.Power z 1.0) for inputs z, so we may try to take z
onlyInputVars :: Expr -> [a] -> [B.Expr] -> [a]
onlyInputVars t xs [] = xs
onlyInputVars t xs ys = 
    let zs = Data.List.filter (\y -> case y of {B.Power z 1.0 -> True; _ -> False}) ys in
    if length zs == length ys then
        let ws = Data.List.map (\z -> case z of {B.Power w 1.0 -> w}) zs in
        xs ++ onlyInputVars t xs zs
    else error ("Cannot substitude variables into " ++ show t ++ ",\n some arguments are not of Var (input variable) type")

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
        Power _ c        -> if xs /= [] then B.Power (headInputVar t xs) c
                            else             B.ComposePower (headAsgnVar t es) c

        PowerLN _ c -> if xs /= [] then B.PowerLN (headInputVar t xs) c
                       else
                           let e = (headAsgnVar t es) in
                           case e of
                               B.Power x 1.0 -> B.PowerLN x c
                               _             -> B.PowerLN (headInputVar t xs) c

        Exp c _          -> if xs /= [] then B.Exp c (headInputVar t xs)
                            else             B.ComposeExp c (headAsgnVar t es)

        Sigmoid a c x    -> if xs /= [] then B.Sigmoid a c (headInputVar t xs)
                            else             B.ComposeSigmoid a c (headAsgnVar t es)

        Const c          -> B.Const c
        ScaleNorm c _    -> B.ScaleNorm c (headAsgnVar t es)
        ZeroSens _       -> B.ZeroSens (headAsgnVar t es)

        L c _            -> if (pairwiseDisjoint vss) && (allUnique xs) then 
                                if xs /= [] then B.L c (onlyInputVars t xs es)
                                else             B.ComposeL c (onlyAsgnVars t xs es)
                            else error err

        LInf _           -> if (allUnique xs) then B.LInf (onlyInputVars t xs es)
                            else error err

        -- checks if the variables of different args are pairwise disjoint
        Prod _           -> if (pairwiseDisjoint vss) then B.Prod (onlyAsgnVars  t xs es)
                            else                           B.Prod2 (onlyAsgnVars  t xs es)

        Min _            -> if (pairwiseDisjoint vss) then B.Min (onlyAsgnVars  t xs es)
                            else error err
        Max _            -> if (pairwiseDisjoint vss) then B.Max (onlyAsgnVars  t xs es)
                            else error err
        Sump c _         -> B.Sump c  (onlyAsgnVars  t xs es)
        SumInf _         -> B.SumInf  (onlyAsgnVars  t xs es)

        -- checks if the variables of different args are pairwise disjoint
        -- let it be Sump 1.0 by default, we can take a finer norm later if necessary
        Sum _            -> if (pairwiseDisjoint vss) then B.Sump 1.0 (onlyAsgnVars  t xs es)
                            else                           B.Sum2 (onlyAsgnVars  t xs es)

        -- this is our reserved "identity" that does nothing
        Id _             -> if xs /= [] then B.Power (headInputVar t xs) 1.0
                            else             (headAsgnVar t es)

   where err = "variables are repeating in different args of the term " ++ show t

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

allUnique :: Ord a => [a] -> Bool
allUnique xs =
    let ys = S.fromList xs in
    S.size ys == length xs

pairwiseDisjoint :: Ord a => [S.Set a] -> Bool
pairwiseDisjoint [] = True
pairwiseDisjoint (vs:vss) =
    let n = length $ Data.List.filter (\vs' -> not (S.null (S.intersection vs vs'))) vss in
    if (n == 0) then pairwiseDisjoint vss else False

