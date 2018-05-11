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

------------------------------------------------------------------------------------------------------
-- TODO: all transformations of Expr and TableExpr are being synchronized with B.Expr and B.TableExpr

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
          | Sum [VarName]                 -- E1+...+En with norm that is not specified yet and will be derived later
          | Id VarName                    -- identity function, used for input table values
          | ARMin                         -- special placeholder for aggregated minimum
          | ARMax                         -- special placeholder for aggregated maximum
          | Text String                   -- this is needed to store strings that remain public and go only into the filters
          | Like VarName VarName          -- stores LIKE expressions for filtering
          | Comp Ordering VarName VarName -- compares two variables, turns to sigmoid/tauoid if necessary
          | LZero VarName                 -- we use it only inside norm definiitons
  deriving Show

-- expressions of type TableExpr use values from the whole table
-- the argument becomes a list when a query gets linked to a database
data TableExpr = SelectProd VarName        -- product (map E rows) with norm ||(N1,...,Nn)||_1 where Ni is N applied to ith row
               | SelectMin VarName         -- min (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]
               | SelectMax VarName         -- max (map E rows) with norm ||(N1,...,Nn)||_p where Ni is N applied to ith row, p is arbitrary in [1,infinity]
               | SelectL Double VarName    -- ||(E1,...,En)||_p with norm ||(N1,...,Nn)||_p
               | SelectSum VarName         -- E1+...+En with norm that is not specified yet and will be derived later
               | SelectCount VarName       -- counts the rows, is rewritten to other expressions
               | Select VarName            -- does not apply aggregation, is used only for intermediate representation
               | SelectDistinct VarName           -- TODO not supported yet, used only to generate nice error messages
               | Filt Ordering VarName Double     -- used for filters, actually is not a 'Table' expression, we just use the same data structure
               | FiltNeg Ordering VarName Double
               | Filter VarName
  deriving Show

--------------------------
-- extract row expressions from an aggregation
getExprFromTableExpr :: B.TableExpr -> [B.Expr]
getExprFromTableExpr expr =
    case expr of
        B.SelectProd es    -> es
        B.SelectL _  es    -> es
        B.SelectMin  es    -> es
        B.SelectMax  es    -> es
        B.SelectSump _ es  -> es
        B.SelectSumInf es  -> es

--------------------------
-- extract arguments
extractArg :: TableExpr -> VarName
extractArg t =
    case t of
        SelectProd x   -> x
        SelectMin x    -> x
        SelectMax x    -> x
        SelectL _ x    -> x
        SelectSum  x   -> x
        SelectCount x  -> x
        SelectDistinct  x  -> x
        Select x       -> x
        Filt _ x _     -> x
        FiltNeg _ x _  -> x
        Filter x       -> x

extractArgs :: Expr -> [VarName]
extractArgs t =
    case t of
        LZero x          -> [x]
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
        Sum xs           -> xs
        Id  x            -> [x]
        ARMin            -> []
        ARMax            -> []
        Text _           -> []
        Like x y         -> [x,y]
        Comp _ x y       -> [x,y]

normArg :: TableExpr -> ADouble
normArg t =
    case t of
        SelectMax _  -> Any
        SelectL c _  -> Exactly c

--------------------------
-- insert arguments
queryArg :: TableExpr -> [B.Expr] -> B.TableExpr
queryArg t ys =
    case t of
        SelectProd _   -> B.SelectProd ys
        SelectMin _    -> B.SelectMin ys
        SelectMax _    -> B.SelectMax ys
        SelectL c _    -> B.SelectL c ys
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

--------------------------
-- puts zeroSens in front of all insensitive variables, remove zeroSens from sensitive variables
-- collect and return also all used sens.variables
-- if a sigmoid/tauoid is applied to an insensitive quantity, we make it more accurate by taking large alpha
markExprCols :: S.Set B.Var -> B.Expr -> ([B.Var],B.Expr)
markExprCols sensitiveVars expr =
    -- do not make alpha too large, since it may cause overflows
    let alpha = 0.1 in
    case expr of
        B.L0Predicate x f  -> if S.member x sensitiveVars then ([x], expr) else ([],B.ZeroSens expr)
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
        B.StringCond s         -> ([], B.StringCond s)

markTableExprCols :: S.Set B.Var -> B.TableExpr -> (B.Expr,B.TableExpr)
markTableExprCols sensitiveVars expr =
    case expr of
        B.SelectProd [e]    -> let z = processRec e in (z, B.SelectProd [z])
        B.SelectL p  [e]    -> let z = processRec e in (z, B.SelectL p [z])
        B.SelectMin  [e]    -> let z = processRec e in (z, B.SelectMin [z])
        B.SelectMax  [e]    -> let z = processRec e in (z, B.SelectMax [z])
        B.SelectSump p [e]  -> let z = processRec e in (z, B.SelectSump p [z])
        B.SelectSumInf [e]  -> let z = processRec e in (z, B.SelectSumInf [z])
    where processRec x = snd $ markExprCols sensitiveVars x

--------------------------
-- get all variables
getAllExprVars :: M.Map VarName Expr -> Expr -> S.Set VarName
getAllExprVars asgnMap expr =
    case expr of
        Power x c        -> processRec x
        PowerLN x c      -> processRec x
        Exp c x          -> processRec x
        Sigmoid a c x    -> processRec x
        Tauoid a c x     -> processRec x
        Const c          -> S.empty
        ScaleNorm a x    -> processRec x
        ZeroSens x       -> processRec x
        L p xs           -> foldr S.union S.empty $ map processRec xs
        LInf xs          -> foldr S.union S.empty $ map processRec xs
        Prod xs          -> foldr S.union S.empty $ map processRec xs
        Min xs           -> foldr S.union S.empty $ map processRec xs
        Max xs           -> foldr S.union S.empty $ map processRec xs
        Sum xs           -> foldr S.union S.empty $ map processRec xs
        Id  x            -> processRec x
        Text c           -> S.empty
        Like x y         -> S.union (processRec x) (processRec y)
        Comp c x y       -> S.union (processRec x) (processRec y)
    where processRec x = takeAlteredIfExists x asgnMap (getAllExprVars asgnMap) S.singleton

getAllTableExprVars :: M.Map VarName Expr -> TableExpr -> S.Set VarName
getAllTableExprVars asgnMap b =
    let x = extractArg b in
    takeAlteredIfExists x asgnMap (getAllExprVars asgnMap) S.singleton

--------------------------
-- updates variable names
updatePrefices :: (S.Set String) -> VarName -> VarName -> VarName
updatePrefices fullTablePaths prefix var = 
    -- if the used table name equals to its full prefix, then it is an actual input
    let varAlias = takeWhile (/= '.') var in
    prefix ++ if S.member varAlias fullTablePaths then var else map (\x -> if x == '.' then '_' else x) var

updatePreficesExpr :: (S.Set String) -> VarName -> Expr -> Expr
updatePreficesExpr fullTablePaths prefix expr =
    case expr of
        LZero x          -> LZero (updatePrefices fullTablePaths prefix x)
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
        Sum xs           -> Sum $ map (updatePrefices fullTablePaths prefix) xs
        Id  x            -> Id (updatePrefices fullTablePaths prefix x)
        Text c           -> Text c
        Like x y         -> Like (updatePrefices fullTablePaths prefix x) (updatePrefices fullTablePaths prefix y)
        Comp c x y       -> Comp c (updatePrefices fullTablePaths prefix x) (updatePrefices fullTablePaths prefix y)

updatePreficesTableExpr :: (S.Set String) -> VarName -> TableExpr -> TableExpr
updatePreficesTableExpr fullTablePaths prefix expr =
    case expr of
        SelectProd x     -> SelectProd     (updatePrefices fullTablePaths prefix x)
        SelectMin x      -> SelectMin      (updatePrefices fullTablePaths prefix x)
        SelectMax x      -> SelectMax      (updatePrefices fullTablePaths prefix x)
        SelectL p x      -> SelectL p      (updatePrefices fullTablePaths prefix x)
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
queryExpression :: M.Map VarName Expr -> Expr -> [B.Var] -> [B.Expr] -> [S.Set B.Var] -> B.Expr
queryExpression asgnMap t xs es vss = 
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
        _ -> error $ "___" ++ show t
   where err = error_queryExpr_repeatingVars t

-- puts preanalysed aggregated function results into correspoding placeholders
applyPrecAggr :: Double -> Double -> B.Expr -> B.Expr
applyPrecAggr arMin arMax expr =

    case expr of
        B.L0Predicate x f  -> B.L0Predicate x f
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
        --B.Prec ar          -> if B.fx ar < 0 then B.Prec arMin else B.Prec arMax
        B.Prec ar          -> if B.fx ar < 0 then B.Const arMin else B.Const arMax

        B.ComposeL p es    -> B.ComposeL p $ map (applyPrecAggr arMin arMax) es
        B.Prod es          -> B.Prod       $ map (applyPrecAggr arMin arMax) es
        B.Prod2 es         -> B.Prod2      $ map (applyPrecAggr arMin arMax) es
        B.Min es           -> B.Min        $ map (applyPrecAggr arMin arMax) es
        B.Max es           -> B.Max        $ map (applyPrecAggr arMin arMax) es
        B.Sump p es        -> B.Sump p     $ map (applyPrecAggr arMin arMax) es
        B.SumInf es        -> B.SumInf     $ map (applyPrecAggr arMin arMax) es
        B.Sum2 es          -> B.Sum2       $ map (applyPrecAggr arMin arMax) es
        B.StringCond s         -> B.StringCond s

applyPrecAggrTable :: Double -> Double ->  B.TableExpr -> B.TableExpr
applyPrecAggrTable arMin arMax expr =
    case expr of
        B.SelectProd es    -> B.SelectProd   $ map (applyPrecAggr arMin arMax) es
        B.SelectL p  es    -> B.SelectL p    $ map (applyPrecAggr arMin arMax) es
        B.SelectMin  es    -> B.SelectMin    $ map (applyPrecAggr arMin arMax) es
        B.SelectMax  es    -> B.SelectMax    $ map (applyPrecAggr arMin arMax) es
        B.SelectSump p es  -> B.SelectSump p $ map (applyPrecAggr arMin arMax) es
        B.SelectSumInf es  -> B.SelectSumInf $ map (applyPrecAggr arMin arMax) es

-- uses preanalysed aggregated function results
precAggr :: [Double] -> [Double] -> [B.TableExpr] -> [B.TableExpr]
precAggr (arMin:arMins) (arMax:arMaxs) (e:es) =
    (applyPrecAggrTable arMin arMax e) : precAggr arMins arMaxs es

-- the definition of Norm allows to use any variables inside argumets (both input and assignment variables)
normExpression :: Expr -> [a] -> [Norm a] -> [S.Set a] -> (Norm a)
normExpression t xs es _ =
    let zs = (map (\ x -> Col x) xs) ++ es in
    case t of
        PowerLN _ _      -> NormLN (head zs)
        LZero _          -> NormLZero (head zs)
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
exprToString :: Bool -> M.Map VarName Expr -> Expr -> String
exprToString isPublic asgnMap expr =
    let alpha = 0.1 in
    case expr of
        PowerLN x c      -> "(" ++ z ++ " ^ " ++ show c ++ ")" where z = processRec x
        Power x c        -> "(" ++ z ++ " ^ " ++ show c ++ ")" where z = processRec x
        Exp c x          -> "exp(" ++ show c ++ " * " ++ z ++ ")" where z = processRec x
        Sigmoid a c x    -> if isPublic then
                                "(case when " ++ z ++ " > " ++ show c ++ " then 1 else 0 end)"
                            else
                                "exp(" ++ w ++ ") / (exp(" ++ w ++ ") + 1)"
                            where
                                z = processRec x
                                w = show a ++ " * (" ++ z ++ " - " ++ show c ++ ")"

        Tauoid a c x     -> if isPublic then
                                "(case when " ++ z ++ " = " ++ show c ++ " then 1 else 0 end)"
                            else
                                "2 / (exp(" ++ w ++ ") + exp(-" ++ w ++ "))"
                            where
                                z = processRec x
                                w = show a ++ " * (" ++ z ++ " - " ++ show c ++ ")"

        Const c          -> show c
        ScaleNorm a x    -> processRec x
        ZeroSens x       -> processRec x
        L p xs           -> "("    ++ intercalate " + " (map (\x -> processRec x ++ "^" ++ show p) xs) ++ ")^" ++ show (1/p)
        LInf xs          -> "greatest(" ++ intercalate " + " (map (\x -> "abs(" ++ processRec x ++ ")") xs) ++ ")"
        Prod xs          -> intercalate " * " $ map processRec xs
        Min xs           -> "least(" ++ (intercalate ", " $ map processRec xs) ++ ")"
        Max xs           -> "greatest(" ++ (intercalate ", " $ map processRec xs) ++ ")"
        Sum xs           -> intercalate " + " $ map processRec xs
        Id  x            -> processRec x
        ARMin            -> "(ArMin PLACEHOLDER)"
        ARMax            -> "(ArMax PLACEHOLDER)"
        Text c           -> "\'" ++ c ++ "\'"
        Like x y         -> "(" ++ processRec x ++ " LIKE " ++ processRec y ++ ")"
        Comp EQ x1 x2    -> if isPublic then
                                "(case when " ++ z1 ++ " = " ++ z2 ++ " then 1 else 0 end)"
                            else
                                "2 / (exp(" ++ w ++ ") + exp(-" ++ w ++ "))"
                            where
                                z1 = processRec x1
                                z2 = processRec x2
                                w = show alpha ++ " * (" ++ z1 ++ " - " ++ show z2 ++ ")"
        Comp GT x1 x2   -> if isPublic then
                                "(case when " ++ z1 ++ " > " ++ z2 ++ " then 1 else 0 end)"
                            else
                                "exp(" ++ w ++ ") / (exp(" ++ w ++ ") + 1)"
                            where
                                z1 = processRec x1
                                z2 = processRec x2
                                w = show alpha ++ " * (" ++ z1 ++ " - " ++ z2 ++ ")"

    where processRec x = takeAlteredIfExists x asgnMap (exprToString isPublic asgnMap) id

tableExprToString :: Bool -> M.Map VarName Expr -> TableExpr -> String
tableExprToString isPublic asgnMap b =
    case b of
        SelectProd x   -> "SELECT PRODUCT(" ++ processRec x ++ ")"
        SelectMin x    -> "SELECT MIN(" ++ processRec x ++ ")"
        SelectMax x    -> "SELECT MAX(" ++ processRec x ++ ")"
        SelectL _ x    -> "UNSUPPORTED SELECT(" ++ processRec x ++ ")"
        SelectSum  x   -> "SELECT SUM(" ++ processRec x ++ ")"
        SelectCount x  -> "SELECT COUNT(" ++ processRec x ++ ")"
        SelectDistinct  x  -> "SELECT DISTINCT(" ++ processRec x ++ ")"
        Select x       -> "SELECT " ++ processRec x
        Filter x       -> processRec x 
    where processRec x = takeAlteredIfExists x asgnMap (exprToString isPublic asgnMap) id

takeAlteredIfExists :: (Show a, Show b, Ord a) => a -> M.Map a b -> (b -> c) -> (a -> c) -> c
takeAlteredIfExists key valMap main alter = if M.member key valMap then main (valMap ! key) else alter key

---------------------------------------------------------------------------------------------
deriveNorm :: (Show a) => [a] -> B.Expr -> Norm a
deriveNorm colnames expr = 
    case expr of
        B.PowerLN x _      -> NormLN (Col (colnames !! x))
        B.L0Predicate x _  -> NormLZero (Col (colnames !! x))
        B.Power x _        -> NormL (Exactly 1.0) [Col (colnames !! x)]
        B.ComposePower e c -> deriveNorm colnames e
        B.Exp _ x          -> NormL (Exactly 1.0) [Col (colnames !! x)]
        B.ComposeExp c e   -> deriveNorm colnames e
        B.Sigmoid _ _ x    -> NormL (Exactly 1.0) [Col (colnames !! x)]
        B.ComposeSigmoid _ _ e -> deriveNorm colnames e
        B.Tauoid  _ _ x    -> NormL (Exactly 1.0) [Col (colnames !! x)]
        B.ComposeTauoid  _ _ e -> deriveNorm colnames e
        B.Const a          -> NormZero
        B.ScaleNorm a e    -> NormScale a (deriveNorm colnames e)
        B.ZeroSens e       -> NormZero
        B.L p xs           -> NormL (Exactly p) $ map (\x -> Col (colnames !! x)) xs
        B.ComposeL p es    -> NormL (Exactly p) $ map (deriveNorm colnames) es
        B.LInf xs          -> NormL Any $ map (\x -> Col (colnames !! x)) xs

        B.Prod es          -> NormL (Exactly 1.0) $ map (deriveNorm colnames) es
        B.Prod2 es         -> let subNorms = map (deriveNorm colnames) es in
                              foldr upperBoundNorm NormZero subNorms
        B.Min es           -> NormL Any $ map (deriveNorm colnames) es
        B.Max es           -> NormL Any $ map (deriveNorm colnames) es
        B.Sump p es        -> NormL (Exactly p) $ map (deriveNorm colnames) es
        B.SumInf es        -> NormL Any $ map (deriveNorm colnames) es
        B.Sum2 es          -> let subNorms = map (deriveNorm colnames) es in
                              foldr upperBoundNorm NormZero subNorms
        B.Prec _           -> NormZero -- we do not need a norm here since its sensitivity is computed separately
        B.StringCond _     -> NormZero -- we do not need a norm here since here are only insensitive variables

deriveTableNorm :: B.TableExpr -> ADouble
deriveTableNorm expr = 
    case expr of

        B.SelectProd _     -> Exactly 1.0
        B.SelectMin  _     -> Any
        B.SelectMax  _     -> Any
        B.SelectL p  _     -> Exactly p
        B.SelectSump p _   -> Exactly p
        B.SelectSumInf _   -> Any

-- puts zeroSens in front of all sensitive variables
-- analogous to markExprCols
markNormCols :: Ord a => S.Set a -> Norm a -> Norm a
markNormCols sensitiveVars expr =
    case expr of
          Col x          -> if S.member x sensitiveVars then expr else NormZero
          NormLN e       -> NormLN (markNormCols sensitiveVars e)
          NormLZero e    -> NormLZero (markNormCols sensitiveVars e)
          NormL p es     -> NormL p $ map (markNormCols sensitiveVars) es
          NormScale c e  -> NormScale c (markNormCols sensitiveVars e)
          NormZero       -> NormZero

-- if x belongs to the map, take map[x], otherwise take a default value y
takeIfExists :: (Show a, Show b, Ord a) => M.Map a b -> a -> b -> b
takeIfExists mapX x y =
    if M.member x mapX then (mapX ! x)
    else y

scale :: M.Map B.Var Double -> B.Var -> Double
scale mapX x = takeIfExists mapX x 1.0

-- takes into account modifications in the norm and applies them to the query expression
updateExpr :: M.Map B.Var Double -> M.Map B.Var Double -> M.Map B.Var Double -> B.Expr -> B.Expr
updateExpr mapCol mapLN mapLZ expr =
    case expr of
        B.PowerLN x c      -> B.ScaleNorm (scale mapLN  x) expr
        B.L0Predicate x f  -> B.ScaleNorm (scale mapLZ  x) expr
        B.Power x c        -> B.ScaleNorm (scale mapCol x) expr
        B.ComposePower e c -> B.ComposePower (updateExpr mapCol mapLN mapLZ e) c
        B.Exp c x          -> B.ScaleNorm (scale mapCol x) (B.Exp c x)
        B.ComposeExp c e   -> B.ComposeExp c (updateExpr mapCol mapLN mapLZ e)
        B.Sigmoid a c x    -> B.ScaleNorm (scale mapCol x) (B.Sigmoid a c x)
        B.ComposeSigmoid a c e -> B.ComposeSigmoid a c (updateExpr mapCol mapLN mapLZ e)
        B.Tauoid a c x     -> B.ScaleNorm (scale mapCol x) (B.Tauoid a c x)
        B.ComposeTauoid a c e -> B.ComposeTauoid a c (updateExpr mapCol mapLN mapLZ e)
        B.Const a          -> B.Const a
        B.ScaleNorm a e    -> B.ScaleNorm a $ updateExpr mapCol mapLN mapLZ e
        B.ZeroSens e       -> B.ZeroSens e
        B.L p xs           -> B.ScaleNorm (foldr min 100000 $ map (scale mapCol) xs) (B.L p xs)
        B.ComposeL p es    -> B.ComposeL p $ map (updateExpr mapCol mapLN mapLZ) es
        B.LInf xs          -> B.ScaleNorm (foldr min 100000 $ map (scale mapCol) xs) (B.LInf xs)
        B.Prod es          -> B.Prod  $ map (updateExpr mapCol mapLN mapLZ) es
        B.Prod2 es         -> B.Prod2 $ map (updateExpr mapCol mapLN mapLZ) es -- we assume that equality of subnorms has been already checked
        B.Min es           -> B.Min $ map (updateExpr mapCol mapLN mapLZ) es
        B.Max es           -> B.Max $ map (updateExpr mapCol mapLN mapLZ) es
        B.Sump p es        -> B.Sump p $ map (updateExpr mapCol mapLN mapLZ) es
        B.SumInf es        -> B.SumInf $ map (updateExpr mapCol mapLN mapLZ) es
        B.Sum2 es          -> B.Sum2   $ map (updateExpr mapCol mapLN mapLZ) es -- we assume that equality of subnorms has been already checked
        B.Prec ar          -> B.Prec ar
        B.StringCond s         -> B.StringCond s

updateTableExpr :: Int -> B.TableExpr -> M.Map B.Var Double -> M.Map B.Var Double -> M.Map B.Var Double -> ADouble -> ADouble -> B.TableExpr
updateTableExpr numOfRows expr mapCol mapLN mapLZ queryAggrNorm dbAggrNorm =
    let n = fromIntegral numOfRows in
    let a = scalingLpNorm queryAggrNorm dbAggrNorm n in
    let g = updateExpr mapCol mapLN mapLZ in
    case expr of
        B.SelectProd es    -> B.SelectProd   $ map (g . B.ScaleNorm a) es
        B.SelectL p  es    -> B.SelectL p    $ map (g . B.ScaleNorm a) es
        B.SelectMin  es    -> B.SelectMin    $ map g es
        B.SelectMax  es    -> B.SelectMax    $ map g es
        B.SelectSump _ es  -> case dbAggrNorm of
                                  Any       -> B.SelectSumInf $ map g es
                                  Exactly p -> B.SelectSump p $ map g es
        B.SelectSumInf es  -> B.SelectSumInf $ map g es

-- Expr to B.Expr
-- the constructor may depend on whether the arguments are input variables or expressions
exprToBExpr :: S.Set B.Var -> M.Map VarName B.Var -> M.Map VarName Expr -> Expr -> (S.Set B.Var, B.Expr)
exprToBExpr sensitiveCols inputMap asgnMap t = 
    let alpha = 0.1 in
    case t of

        -- TODO we would like error message if s is misused later
        Text s      -> (S.empty, B.StringCond ("\'" ++ s ++ "\'"))
        Power x c   -> processRec (\z -> B.ComposePower z c) (\z -> B.Power z c) x

        PowerLN x c -> processRec (const (error err)) (\z -> B.PowerLN z c) x

        Exp c x          -> processRec (B.ComposeExp c) (B.Exp c) x

        Sigmoid a c x    -> let (usedVars,y) = processRec (B.ComposeSigmoid a c) (B.Sigmoid a c) x in
                            let w = if S.size (S.intersection usedVars sensitiveCols) == 0 then B.StringCond (exprToString True asgnMap t) else y in
                            (usedVars,w)

        Tauoid a c x     -> let (usedVars,y) = processRec (B.ComposeTauoid a c) (B.Tauoid a c) x in
                            let w = if S.size (S.intersection usedVars sensitiveCols) == 0 then B.StringCond (exprToString True asgnMap t) else y in
                            (usedVars,w)

        Const c          -> (S.empty, B.Const c)
        ScaleNorm c x    -> processRec (B.ScaleNorm c) (\z -> B.ScaleNorm c (B.Power z 1.0)) x
        ZeroSens x       -> processRec B.ZeroSens (\z -> B.ZeroSens (B.Power z 1.0)) x

        L c xs           -> let (vss,es) = unzip $ map (processRec id (\z -> B.Power z 1.0)) xs in
                            let usedVars = foldr S.union S.empty vss in
                            if (pairwiseDisjoint vss) && (allUnique xs) then
                                if allInputVars xs then (usedVars, B.L c $ map (inputMap !) xs)
                                else (usedVars, B.ComposeL c es)
                            else error err

        LInf xs          -> if (allUnique xs) then
                                if allInputVars xs then (S.fromList $ map (inputMap !) xs, B.LInf $ map (inputMap !) xs)
                                else error err
                            else error err

        -- checks if the variables of different args are pairwise disjoint
        Prod xs          -> let (vss,es)  = unzip $ map (processRec id (\z -> B.Power z 1.0)) xs in
                            let usedVars = foldr S.union S.empty vss in
                            if (pairwiseDisjoint vss) then (usedVars,B.Prod  es)
                            else                           (usedVars,B.Prod2 es)

        Min xs           -> let (vss,es)  = unzip $ map (processRec id (\z -> B.Power z 1.0)) xs in
                            let usedVars = foldr S.union S.empty vss in
                            if (pairwiseDisjoint vss) then (usedVars,B.Min es)
                            else error err
        Max xs           -> let (vss,es)  = unzip $ map (processRec id (\z -> B.Power z 1.0)) xs in
                            let usedVars = foldr S.union S.empty vss in
                            if (pairwiseDisjoint vss) then (usedVars,B.Max es)
                            else error err

        -- checks if the variables of different args are pairwise disjoint
        -- let it be Sump 1.0 by default, we can take a finer norm later if necessary
        Sum xs           -> let (vss,es)  = unzip $ map (processRec id (\z -> B.Power z 1.0)) xs in
                            let usedVars = foldr S.union S.empty vss in
                            if (pairwiseDisjoint vss) then (usedVars,B.Sump 1.0 es)
                            else                           (usedVars,B.Sum2 es)

        -- this is our reserved 'identity' that does nothing
        Id x             ->  processRec id (\z -> B.Power z 1.0) x

        -- in the following, 1.0 and -1.0 are used only to show whether it was min or max, and will be modified later
        ARMax            -> (S.empty, B.Prec (B.AR {B.fx =  1.0, B.subf = B.SUB {B.subg = id, B.subBeta = 0.0}, B.sdsf = B.SUB {B.subg = id, B.subBeta = 0.0}}))
        ARMin            -> (S.empty, B.Prec (B.AR {B.fx = -1.0, B.subf = B.SUB {B.subg = id, B.subBeta = 0.0}, B.sdsf = B.SUB {B.subg = id, B.subBeta = 0.0}}))
        Comp GT x1 x2    -> let (usedVars1,e1) = processRec id (\z -> B.Power z 1.0) x1 in
                            let (usedVars2,e2) = processRec id (\z -> B.Power z 1.0) x2 in
                            let usedVars = S.union usedVars1 usedVars2 in
                            if S.size (S.intersection usedVars sensitiveCols) == 0 then
                                (usedVars, B.StringCond (exprToString True asgnMap t))
                            else
                                -- use l0-norm if we are comparing strings
                                -- TODO we will probably handle more complicated cases later
                                case (e1,e2) of
                                    (B.StringCond z1, B.Power x2 1.0) -> (usedVars, B.L0Predicate x2 (\z -> z ++ " > " ++ z1))
                                    (B.StringCond z1,              _) -> error $ error_queryExpr_syntax t
                                    (B.Power x1 1.0, B.StringCond z2) -> (usedVars, B.L0Predicate x1 (\z -> z ++ " > " ++ z2))
                                    (_,              B.StringCond z2) -> error $ error_queryExpr_syntax t
                                    _ ->
                                        if (pairwiseDisjoint [usedVars1,usedVars2]) then
                                            (usedVars, B.ComposeSigmoid alpha 0.0 (B.Sump 1.0 [e1, B.Prod[B.Const (-1.0), e2]]))
                                        else
                                            (usedVars, B.ComposeSigmoid alpha 0.0 (B.Sum2 [e1, B.Prod[B.Const (-1.0), e2]]))

        Comp EQ x1 x2    -> let (usedVars1,e1) = processRec id (\z -> B.Power z 1.0) x1 in
                            let (usedVars2,e2) = processRec id (\z -> B.Power z 1.0) x2 in
                            let usedVars = S.union usedVars1 usedVars2 in
                            if S.size (S.intersection usedVars sensitiveCols) == 0 then
                                (usedVars, B.StringCond (exprToString True asgnMap t))
                            else
                                -- use l0-norm if we are comparing strings
                                -- TODO we will probably handle more complicated cases later
                                case (e1,e2) of
                                    (B.StringCond z1, B.Power x2 1.0) -> (usedVars, B.L0Predicate x2 (\z -> z ++ " = " ++ z1))
                                    (B.StringCond z1,              _) -> error $ error_queryExpr_syntax t
                                    (B.Power x1 1.0, B.StringCond z2) -> (usedVars, B.L0Predicate x1 (\z -> z ++ " = " ++ z2))
                                    (_,              B.StringCond z2) -> error $ error_queryExpr_syntax t
                                    _ ->
                                        if (pairwiseDisjoint [usedVars1,usedVars2]) then
                                            (usedVars, B.ComposeTauoid alpha 0.0 (B.Sump 1.0 [e1, B.Prod[B.Const (-1.0), e2]]))
                                        else
                                            (usedVars, B.ComposeTauoid alpha 0.0 (B.Sum2 [e1, B.Prod[B.Const (-1.0), e2]]))
        _ -> error $ error_queryExpr_syntax t
   where err = error_queryExpr_repeatingVars t
         allInputVars xs  = foldr (\x y -> (not (M.member x asgnMap)) && y) True xs
         processRec f g x = if M.member x asgnMap then
                                   let (usedVars,e) = exprToBExpr sensitiveCols inputMap asgnMap (asgnMap ! x) in
                                   (usedVars,f e)
                               else
                                   let e = inputMap ! x in
                                   (S.singleton e, g e)

tableExprToBTableExpr :: S.Set B.Var -> M.Map VarName B.Var -> M.Map VarName Expr -> TableExpr -> B.TableExpr
tableExprToBTableExpr sensitiveCols inputMap asgnMap t = 
    case t of
        SelectProd x   -> B.SelectProd $ processRec x
        SelectMin x    -> B.SelectMin $ processRec x
        SelectMax x    -> B.SelectMax $ processRec x
        SelectL c x    -> B.SelectL c $ processRec x
        -- let it be Sump 1.0 by default, we can take a finer norm later if necessary
        SelectSum  x   -> B.SelectSump 1.0 $ processRec x
        -- if it turns out that, if SelectCount is left as it is,
        -- then all filters are defined over non-sensitive variables, so they are discarded completely
        SelectCount x  -> B.SelectSump 1.0 $ map (\_ -> B.ZeroSens (B.Const 1.0)) (processRec x)
        SelectDistinct  _  -> error $ error_queryExpr_syntax t
        Select _       -> error $ error_queryExpr_syntax t
        Filt _ _ _     -> error $ error_internal_queryExprFilter t
        FiltNeg _ _ _  -> error $ error_internal_queryExprFilter t
        Filter _       -> error $ error_internal_queryExprFilter t
    where processRec x = [snd $ exprToBExpr sensitiveCols inputMap asgnMap (asgnMap ! x)]
