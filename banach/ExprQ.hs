module ExprQ where

import Prelude hiding ((!!))
import Data.List hiding ((!!))
import qualified Data.Set as S
import qualified Data.Map as M

-- import Expr from Banach.hs
import qualified Banach as B
import ErrorMsg
import NormsQ

-- let the variable names be alphanumeric strings starting with a character
type VarName = String

-----------------------------------------------------------------------------------
-- TODO: Expr and TableExpr are being synchronized with B.Expr and B.TableExpr

-- these are single-step Banach expressions, all 'Expr' and 'Var' substituted with 'VarName'
data Expr = Power VarName Double          -- x^r with norm | |, or E^r with norm N
          | PowerLN VarName Double        -- x^r with logarithmic norm: ||x|| = |ln x|, addition in Banach space is multiplication of real numbers
          | Exp Double VarName            -- e^(r*x) with norm | |
          | Sigmoid Double Double VarName -- s(a,c,x) = e^(a*(x-c))/(e^(a*(x-c)) + 1)
          | Tauoid Double Double VarName  -- t(a,c,x) = 2/(e^(-a*(x-c)) + e^(a*(x-c)))
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
          | ARMin                         -- special placeholder for aggregated minimum
          | ARMax                         -- special placeholder for aggregated maximum
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
               | SelectDistinct VarName           -- TODO not supported yet, used only to generate nice error messages
               | Filt Ordering VarName Double     -- used for filters, actually is not a 'Table' expression, we just use the same data structure
               | FiltNeg Ordering VarName Double
               | Filter VarName
  deriving Show

getExprFromTableExpr :: B.TableExpr -> [B.Expr]
getExprFromTableExpr expr =
    case expr of
        B.SelectProd es    -> es
        B.SelectL _  es    -> es
        B.SelectMin  es    -> es
        B.SelectMax  es    -> es
        B.SelectSump _ es  -> es
        B.SelectSumInf es  -> es

-----------------------------------------------------------------------------------
-- TODO: reconstruction of terms is being synchronized with B.Expr and B.TableExpr

extractArg :: TableExpr -> VarName
extractArg t =
    case t of
        SelectProd x   -> x
        SelectMin x    -> x
        SelectMax x    -> x
        SelectL _ x    -> x
        SelectSump _ x -> x
        SelectSumInf x -> x
        SelectSum  x   -> x
        SelectCount x  -> x
        SelectDistinct  x  -> x
        Select x       -> x
        Filt _ x _     -> x
        FiltNeg _ x _  -> x
        Filter x       -> x

queryArg :: TableExpr -> [B.Expr] -> B.TableExpr
queryArg t ys =
    case t of
        SelectProd _   -> B.SelectProd ys
        SelectMin _    -> B.SelectMin ys
        SelectMax _    -> B.SelectMax ys
        SelectL c _    -> B.SelectL c ys
        SelectSump c _ -> B.SelectSump c ys
        SelectSumInf _ -> B.SelectSumInf ys
        -- let it be Sump 1.0 by default, we can take a finer norm later if necessary
        SelectSum  _   -> B.SelectSump 1.0 ys
        -- if it turns out that, if SelectCount is left as it is,
        -- then all filters are defined over non-sensitive variables, so they are discarded completely
        SelectCount _  -> B.SelectSump 1.0 $ map (\_ -> B.ZeroSens (B.Const 1.0)) ys
        SelectDistinct  _  -> error $ error_queryExpr_syntax t
        Select _       -> error $ error_queryExpr_syntax t
        Filt _ _ _     -> error $ error_internal_queryExprFilter t
        FiltNeg _ _ _  -> error $ error_internal_queryExprFilter t
        Filter _       -> error $ error_internal_queryExprFilter t

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
        Tauoid _ _ x     -> [x]
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
        ARMin            -> []
        ARMax            -> []

-- puts zeroSens in front of all insensitive variables, remove zeroSens from sensitive variables
-- collect and return also all used sens.variables
-- if a sigmoid/tauoid is applied to an insensitive quantity, we make it more accurate by taking large alpha
markExprCols :: S.Set B.Var -> B.Expr -> ([B.Var],B.Expr)
markExprCols sensitiveVars expr =
    -- do not make alpha too large, since it may cause overflows
    let alpha = 10.0 in
    case expr of
        B.PowerLN x c      -> if S.member x sensitiveVars then ([x], expr) else ([],B.ZeroSens expr)
        B.Power x c        -> if S.member x sensitiveVars then ([x], expr) else ([],B.ZeroSens expr)
        B.ComposePower e c -> let (t1,t2) = markExprCols sensitiveVars e in (t1, B.ComposePower t2 c)
        B.Exp c x          -> if S.member x sensitiveVars then ([x], expr) else ([],B.ZeroSens expr)
        B.ComposeExp c e   -> let (t1,t2) = markExprCols sensitiveVars e in (t1, B.ComposeExp c t2)
        B.Sigmoid a c x    -> if S.member x sensitiveVars then ([x], expr) else ([],B.ZeroSens (B.Sigmoid alpha c x))
        B.ComposeSigmoid a c e -> let (t1,t2) = markExprCols sensitiveVars e in 
                                      if length t1 == 0 then
                                          (t1, B.ComposeSigmoid alpha c t2)
                                      else
                                          (t1, B.ComposeSigmoid a c t2)
        B.Tauoid a c x     -> if S.member x sensitiveVars then ([x], expr) else ([],B.ZeroSens (B.Tauoid alpha c x))
        B.ComposeTauoid a c e  -> let (t1,t2) = markExprCols sensitiveVars e in 
                                      if length t1 == 0 then
                                          (t1,B.ComposeTauoid alpha c t2)
                                      else
                                          (t1,B.ComposeTauoid a c t2)
        B.Const c          -> ([],B.Const c)
        B.ScaleNorm a e    -> let (t1,t2) = markExprCols sensitiveVars e in (t1,B.ScaleNorm a t2)
        B.ZeroSens e       -> let (t1,t2) = markExprCols sensitiveVars e in
                                  if length t1 == 0 then
                                      ([],B.ZeroSens t2)
                                  else
                                      (t1,t2)

        B.L p xs           -> let allSensitive = foldr (\x y -> if S.member x sensitiveVars then True && y else False) True xs in
                              if allSensitive then
                                  (xs, B.L p xs)
                              else
                                  let t1 = filter (\x -> S.member x sensitiveVars) xs in
                                  let t2 = map (\x -> let z = B.Power x 1.0 in if S.member x sensitiveVars then z else B.ZeroSens z) xs in
                                  (t1, B.ComposeL p t2) 

        B.LInf xs          -> let allInsensitive = foldr (\x y -> if S.member x sensitiveVars then False else True && y) True xs in
                              if allInsensitive then
                                  ([], B.ZeroSens (B.LInf xs))
                              else
                                  let t1 = filter (\x -> S.member x sensitiveVars) xs in
                                  (t1, B.LInf xs)

        B.ComposeL p es    -> let (t1s,t2s) = unzip $ map (markExprCols sensitiveVars) es in (concat t1s, B.ComposeL p t2s)
        B.Prod es          -> let (t1s,t2s) = unzip $ map (markExprCols sensitiveVars) es in (concat t1s, B.Prod       t2s)
        B.Prod2 es         -> let (t1s,t2s) = unzip $ map (markExprCols sensitiveVars) es in (concat t1s, B.Prod2      t2s)
        B.Min es           -> let (t1s,t2s) = unzip $ map (markExprCols sensitiveVars) es in (concat t1s, B.Min        t2s)
        B.Max es           -> let (t1s,t2s) = unzip $ map (markExprCols sensitiveVars) es in (concat t1s, B.Max        t2s)
        B.Sump p es        -> let (t1s,t2s) = unzip $ map (markExprCols sensitiveVars) es in (concat t1s, B.Sump p     t2s)
        B.SumInf es        -> let (t1s,t2s) = unzip $ map (markExprCols sensitiveVars) es in (concat t1s, B.SumInf     t2s)
        B.Sum2 es          -> let (t1s,t2s) = unzip $ map (markExprCols sensitiveVars) es in (concat t1s, B.Sum2       t2s)
        -- TODO we actually do not want ZeroSens in front of it!
        B.Prec ar          -> ([], B.Prec ar)

markTableExprCols :: S.Set B.Var -> B.TableExpr -> B.TableExpr
markTableExprCols sensitiveVars expr =
    case expr of
        B.SelectProd es    -> B.SelectProd   $ map (snd . markExprCols sensitiveVars) es
        B.SelectL p  es    -> B.SelectL p    $ map (snd . markExprCols sensitiveVars) es
        B.SelectMin  es    -> B.SelectMin    $ map (snd . markExprCols sensitiveVars) es
        B.SelectMax  es    -> B.SelectMax    $ map (snd . markExprCols sensitiveVars) es
        B.SelectSump p es  -> B.SelectSump p $ map (snd . markExprCols sensitiveVars) es
        B.SelectSumInf es  -> B.SelectSumInf $ map (snd . markExprCols sensitiveVars) es

-- updates variable names
updatePrefices :: (S.Set String) -> VarName -> VarName -> VarName
updatePrefices fullTablePaths prefix var = 
    -- if the used table name equals to its full prefix, then it is an actual input
    let varAlias = takeWhile (/= '.') var in
    prefix ++ if S.member varAlias fullTablePaths then var else map (\x -> if x == '.' then '_' else x) var

updatePreficesExpr :: (S.Set String) -> VarName -> Expr -> Expr
updatePreficesExpr fullTablePaths prefix expr =
    case expr of
        Power x c        -> Power (updatePrefices fullTablePaths prefix x) c
        PowerLN x c      -> PowerLN (updatePrefices fullTablePaths prefix x) c
        Exp c x          -> Exp c (updatePrefices fullTablePaths prefix x)
        Sigmoid a c x    -> Sigmoid a c (updatePrefices fullTablePaths prefix x)
        Tauoid a c x     -> Tauoid a c (updatePrefices fullTablePaths prefix x)
        Const c          -> Const c
        ScaleNorm a x    -> ScaleNorm a (updatePrefices fullTablePaths prefix x)
        ZeroSens x       -> ZeroSens (updatePrefices fullTablePaths prefix x)
        L p xs           -> L p $ map (updatePrefices fullTablePaths prefix) xs
        LInf xs          -> LInf $ map (updatePrefices fullTablePaths prefix) xs
        Prod xs          -> Prod $ map (updatePrefices fullTablePaths prefix) xs
        Min xs           -> Min $ map (updatePrefices fullTablePaths prefix) xs
        Max xs           -> Max $ map (updatePrefices fullTablePaths prefix) xs
        Sump p xs        -> Sump p $ map (updatePrefices fullTablePaths prefix) xs
        SumInf xs        -> SumInf $ map (updatePrefices fullTablePaths prefix) xs
        Sum xs           -> Sum $ map (updatePrefices fullTablePaths prefix) xs
        Id  x            -> Id (updatePrefices fullTablePaths prefix x)

updatePreficesTableExpr :: (S.Set String) -> VarName -> TableExpr -> TableExpr
updatePreficesTableExpr fullTablePaths prefix expr =
    case expr of
        SelectProd x     -> SelectProd     (updatePrefices fullTablePaths prefix x)
        SelectMin x      -> SelectMin      (updatePrefices fullTablePaths prefix x)
        SelectMax x      -> SelectMax      (updatePrefices fullTablePaths prefix x)
        SelectL p x      -> SelectL p      (updatePrefices fullTablePaths prefix x)
        SelectSump p x   -> SelectSump p   (updatePrefices fullTablePaths prefix x)
        SelectSumInf x   -> SelectSumInf   (updatePrefices fullTablePaths prefix x)
        SelectSum  x     -> SelectSum      (updatePrefices fullTablePaths prefix x)
        SelectCount x    -> SelectCount    (updatePrefices fullTablePaths prefix x)
        SelectDistinct x -> SelectDistinct (updatePrefices fullTablePaths prefix x)
        Select x         -> Select         (updatePrefices fullTablePaths prefix x)
        Filt a x c       -> Filt a         (updatePrefices fullTablePaths prefix x) c
        FiltNeg a x c    -> FiltNeg a      (updatePrefices fullTablePaths prefix x) c
        Filter x         -> Filter         (updatePrefices fullTablePaths prefix x)

-- this is needed to make error of a missing head clearer
-- the errors come where the argument has to be an input variable, but it is actually an expression, and vice versa
headInputVar :: Expr -> [a] -> [b] -> a
headInputVar t [] [] = error $ error_queryExpr_undefinedVars t
headInputVar t [] _  = error $ error_queryExpr_missingInputVars t
headInputVar t xs _  = head xs

headAsgnVar :: Expr -> [a] -> [b] -> b
headAsgnVar t [] [] = error $ error_queryExpr_undefinedVars t
headAsgnVar t _  [] = error $ error_queryExpr_missingAsgnVars t
headAsgnVar t _  xs = head xs

-- if some variables are not immediate inputs, they may just be represented as (B.Power z 1.0) for inputs z, so we may try to take z
onlyInputVars :: Expr -> [a] -> [B.Expr] -> [a]
onlyInputVars t [] [] = error $ error_queryExpr_undefinedVars t
onlyInputVars t xs [] = xs
onlyInputVars t xs ys = 
    let zs = filter (\y -> case y of {B.Power z 1.0 -> True; _ -> False}) ys in
    if length zs == length ys then
        let ws = map (\z -> case z of {B.Power w 1.0 -> w}) zs in
        xs ++ onlyInputVars t xs zs
    else error $ error_queryExpr_notAllInputVars t

onlyAsgnVars :: Expr -> [a] -> [b] -> [b]
onlyAsgnVars t [] [] = error $ error_queryExpr_undefinedVars t
onlyAsgnVars t [] xs = xs
onlyAsgnVars t _ _   = error $ error_queryExpr_notAllAsgnVars t

-- the constructor may depend on whether the arguments are input variables or expressions
-- arg1: the term
-- arg2: used input variables
-- arg3: used assignment variables
-- arg4: the list of input vars in turn used by asgn variables -- needed e.g to decide whether Prod becomes B.Prod or B.Prod2
queryExpression :: Expr -> [B.Var] -> [B.Expr] -> [S.Set B.Var] -> B.Expr
queryExpression t xs es vss = 
    case t of
        Power _ c        -> if xs /= [] then B.Power (headInputVar t xs es) c
                            else             B.ComposePower (headAsgnVar t xs es) c

        PowerLN _ c -> if xs /= [] then B.PowerLN (headInputVar t xs es) c
                       else
                           let e = (headAsgnVar t xs es) in
                           case e of
                               B.Power x 1.0 -> B.PowerLN x c
                               _             -> B.PowerLN (headInputVar t xs es) c

        Exp c _          -> if xs /= [] then B.Exp c (headInputVar t xs es)
                            else             B.ComposeExp c (headAsgnVar t xs es)

        Sigmoid a c x    -> if xs /= [] then B.Sigmoid a c (headInputVar t xs es)
                            else             B.ComposeSigmoid a c (headAsgnVar t xs es)

        Tauoid a c x     -> if xs /= [] then B.Tauoid a c (headInputVar t xs es)
                            else             B.ComposeTauoid a c (headAsgnVar t xs es)

        Const c          -> B.Const c
        ScaleNorm c _    -> B.ScaleNorm c (headAsgnVar t xs es)
        ZeroSens _       -> B.ZeroSens (headAsgnVar t xs es)

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

        -- this is our reserved 'identity' that does nothing
        Id _             -> if xs /= [] then B.Power (headInputVar t xs es) 1.0
                            else             (headAsgnVar t xs es)
        -- in the following, 1.0 and -1.0 are used only to show whether it was min or max, and will be modified later
        ARMax            -> B.Prec (B.AR {B.fx =  1.0, B.subf = B.SUB {B.subg = id, B.subBeta = 0.0}, B.sdsf = B.SUB {B.subg = id, B.subBeta = 0.0}})
        ARMin            -> B.Prec (B.AR {B.fx = -1.0, B.subf = B.SUB {B.subg = id, B.subBeta = 0.0}, B.sdsf = B.SUB {B.subg = id, B.subBeta = 0.0}})

   where err = error_queryExpr_repeatingVars t



-- make sigmoid/tauoid more accurate by taking large alpha
-- this is needed to estimate what the query is "actually" supposed to output
preciseSigmoidsExpr :: B.Expr -> B.Expr
preciseSigmoidsExpr expr =

    -- do not make alpha too large, since it may cause overflows
    let alpha = 10.0 in
    case expr of
        B.PowerLN x c      -> B.PowerLN x c
        B.Power x c        -> B.Power x c
        B.ComposePower e c -> B.ComposePower (preciseSigmoidsExpr e) c
        B.Exp c x          -> B.Exp c x
        B.ComposeExp c e   -> B.ComposeExp c (preciseSigmoidsExpr e)
        B.Sigmoid a c x    -> B.Sigmoid alpha c x
        B.ComposeSigmoid a c e -> B.ComposeSigmoid alpha c (preciseSigmoidsExpr e)
        B.Tauoid a c x     -> B.Tauoid alpha c x
        B.ComposeTauoid a c e  -> B.ComposeTauoid  alpha c (preciseSigmoidsExpr e)
        B.Const c          -> B.Const c
        B.ScaleNorm a e    -> B.ScaleNorm a (preciseSigmoidsExpr e)
        B.ZeroSens e       -> B.ZeroSens (preciseSigmoidsExpr e)
        B.L p xs           -> B.L p xs
        B.LInf xs          -> B.LInf xs
        B.Prec ar          -> B.Prec ar

        B.ComposeL p es    -> B.ComposeL p $ map preciseSigmoidsExpr es
        B.Prod es          -> B.Prod $ map preciseSigmoidsExpr es
        B.Prod2 es         -> B.Prod2 $ map preciseSigmoidsExpr es
        B.Min es           -> B.Min $ map preciseSigmoidsExpr es
        B.Max es           -> B.Max $ map preciseSigmoidsExpr es
        B.Sump p es        -> B.Sump p $ map preciseSigmoidsExpr es
        B.SumInf es        -> B.SumInf $ map preciseSigmoidsExpr es
        B.Sum2 es          -> B.Sum2 $ map preciseSigmoidsExpr es

preciseSigmoidsTableExpr :: B.TableExpr -> B.TableExpr
preciseSigmoidsTableExpr expr =
    case expr of
        B.SelectProd es    -> B.SelectProd   $ map preciseSigmoidsExpr es
        B.SelectL p  es    -> B.SelectL p    $ map preciseSigmoidsExpr es
        B.SelectMin  es    -> B.SelectMin    $ map preciseSigmoidsExpr es
        B.SelectMax  es    -> B.SelectMax    $ map preciseSigmoidsExpr es
        B.SelectSump p es  -> B.SelectSump p $ map preciseSigmoidsExpr es
        B.SelectSumInf es  -> B.SelectSumInf $ map preciseSigmoidsExpr es

-- puts preanalysed aggregated function results into correspoding placeholders
applyPrecAggr :: B.AnalysisResult -> B.AnalysisResult -> B.Expr -> B.Expr
applyPrecAggr arMin arMax expr =

    case expr of
        B.PowerLN x c      -> B.PowerLN x c
        B.Power x c        -> B.Power x c
        B.ComposePower e c -> B.ComposePower (applyPrecAggr arMin arMax e) c
        B.Exp c x          -> B.Exp c x
        B.ComposeExp c e   -> B.ComposeExp c (applyPrecAggr arMin arMax e)
        B.Sigmoid a c x    -> B.Sigmoid a c x
        B.ComposeSigmoid a c e -> B.ComposeSigmoid a c (applyPrecAggr arMin arMax e)
        B.Tauoid a c x     -> B.Tauoid a c x
        B.ComposeTauoid a c e  -> B.ComposeTauoid  a c (applyPrecAggr arMin arMax e)
        B.Const c          -> B.Const c
        B.ScaleNorm a e    -> B.ScaleNorm a (applyPrecAggr arMin arMax e)
        B.ZeroSens e       -> B.ZeroSens (applyPrecAggr arMin arMax e)
        B.L p xs           -> B.L p xs
        B.LInf xs          -> B.LInf xs
        B.Prec ar          -> if B.fx ar < 0 then B.Prec arMin else B.Prec arMax

        B.ComposeL p es    -> B.ComposeL p $ map (applyPrecAggr arMin arMax) es
        B.Prod es          -> B.Prod       $ map (applyPrecAggr arMin arMax) es
        B.Prod2 es         -> B.Prod2      $ map (applyPrecAggr arMin arMax) es
        B.Min es           -> B.Min        $ map (applyPrecAggr arMin arMax) es
        B.Max es           -> B.Max        $ map (applyPrecAggr arMin arMax) es
        B.Sump p es        -> B.Sump p     $ map (applyPrecAggr arMin arMax) es
        B.SumInf es        -> B.SumInf     $ map (applyPrecAggr arMin arMax) es
        B.Sum2 es          -> B.Sum2       $ map (applyPrecAggr arMin arMax) es

applyPrecAggrTable :: B.AnalysisResult -> B.AnalysisResult -> B.TableExpr -> B.TableExpr
applyPrecAggrTable arMin arMax expr =
    case expr of
        B.SelectProd es    -> B.SelectProd   $ map (applyPrecAggr arMin arMax) es
        B.SelectL p  es    -> B.SelectL p    $ map (applyPrecAggr arMin arMax) es
        B.SelectMin  es    -> B.SelectMin    $ map (applyPrecAggr arMin arMax) es
        B.SelectMax  es    -> B.SelectMax    $ map (applyPrecAggr arMin arMax) es
        B.SelectSump p es  -> B.SelectSump p $ map (applyPrecAggr arMin arMax) es
        B.SelectSumInf es  -> B.SelectSumInf $ map (applyPrecAggr arMin arMax) es

-- uses preanalysed aggregated function results
precAggr :: [B.AnalysisResult] -> [B.AnalysisResult] -> [B.TableExpr] -> [B.TableExpr]
precAggr (arMin:arMins) (arMax:arMaxs) (e:es) =
    (applyPrecAggrTable arMin arMax e) : precAggr arMins arMaxs es

-- the definition of Norm allows to use any variables inside argumets (both input and assignment variables)
normExpression :: Expr -> [a] -> [Norm a] -> [S.Set a] -> (Norm a)
normExpression t xs es _ =
    let zs = (map (\ x -> Col x) xs) ++ es in
    case t of
        PowerLN _ _      -> NormLN (head zs)
        ScaleNorm c _    -> NormScale c (head zs)
        ZeroSens _       -> NormZero
        L c _            -> NormL (Exactly c) zs
        LInf _           -> NormL Any zs

allUnique :: Ord a => [a] -> Bool
allUnique xs =
    let ys = S.fromList xs in
    S.size ys == length xs

pairwiseDisjoint :: Ord a => [S.Set a] -> Bool
pairwiseDisjoint [] = True
pairwiseDisjoint (vs:vss) =
    let n = length $ filter (\vs' -> not (S.null (S.intersection vs vs'))) vss in
    if (n == 0) then pairwiseDisjoint vss else False

-- converts expressions to Strings that can be read as a part of SQL query
exprToString :: [String] -> B.Expr -> String
exprToString colnames expr =

    case expr of
        B.PowerLN x c      -> "(" ++ z ++ " ^ " ++ show c ++ ")" where z = colnames !! x
        B.Power x c        -> "(" ++ z ++ " ^ " ++ show c ++ ")" where z = colnames !! x
        B.ComposePower e c -> "(" ++ z ++ " ^ " ++ show c ++ ")" where z = exprToString colnames e
        B.Exp c x          -> "exp(" ++ show c ++ " * " ++ z ++ ")" where z = colnames !! x
        B.ComposeExp c e   -> "exp(" ++ show c ++ " * " ++ z ++ ")" where z = exprToString colnames e
        B.Sigmoid a c x        -> "exp(" ++ z ++ ") / (exp(" ++ z ++ ") + 1)" where z = show a ++ " * (" ++ (colnames !! x) ++ " - " ++ show c ++ ")"
        B.ComposeSigmoid a c e -> "exp(" ++ z ++ ") / (exp(" ++ z ++ ") + 1)" where z = show a ++ " * (" ++ (exprToString colnames e) ++ " - " ++ show c ++ ")"
        B.Tauoid a c x         -> "2 / (exp(" ++ z ++ ") + exp(-" ++ z ++ "))" where z = show a ++ " * (" ++ (colnames !! x) ++ " - " ++ show c ++ ")"
        B.ComposeTauoid a c e  -> "2 / (exp(" ++ z ++ ") + exp(-" ++ z ++ "))" where z = show a ++ " * (" ++ (exprToString colnames e) ++ " - " ++ show c ++ ")"
        B.Const c          -> show c
        B.ScaleNorm a e    -> exprToString colnames e
        B.ZeroSens e       -> exprToString colnames e
        B.L p xs           -> "("    ++ intercalate " + " (map (\x -> (colnames !! x) ++ "^" ++ show p) xs) ++ ")^" ++ show (1/p)
        B.LInf xs          -> "greatest(" ++ intercalate " + " (map (\x -> "abs(" ++ (colnames !! x) ++ ")") xs) ++ ")"
        B.Prec ar          -> show $ B.fx ar

        B.ComposeL p es    -> "(" ++ intercalate " + " (map (\e -> (exprToString colnames e) ++ "^" ++ show p) es) ++ ")^" ++ show (1/p)
        B.Prod es          -> intercalate " * " $ map (exprToString colnames) es
        B.Prod2 es         -> intercalate " * " $ map (exprToString colnames) es
        B.Min es           -> "least(" ++ (intercalate ", " $ map (exprToString colnames) es) ++ ")"
        B.Max es           -> "greatest(" ++ (intercalate ", " $ map (exprToString colnames) es) ++ ")"
        B.Sump p es        -> intercalate " + " $ map (exprToString colnames) es
        B.SumInf es        -> intercalate " + " $ map (exprToString colnames) es
        B.Sum2 es          -> intercalate " + " $ map (exprToString colnames) es

-- if an expression does not contain sensitive variables (a public filter), we do not need to use sigmoids
pubExprToString :: [String] -> B.Expr -> String
pubExprToString colnames expr =

    case expr of
        B.Sigmoid a c x        -> "(" ++ z ++ " < " ++ show c ++ ")" where z = colnames !! x
        B.ComposeSigmoid a c e -> "(" ++ z ++ " < " ++ show c ++ ")" where z = exprToString colnames e
        B.Tauoid a c x         -> "(" ++ z ++ " = " ++ show c ++ ")" where z = colnames !! x
        B.ComposeTauoid a c e  -> "(" ++ z ++ " = " ++ show c ++ ")" where z = exprToString colnames e
        _                      -> exprToString colnames expr

