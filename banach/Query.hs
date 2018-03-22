module Query where

import Control.Monad (void)
import Data.Bits
import Data.Either
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Void
--import Debug.Trace

import qualified Banach as B
import ErrorMsg
import Expr


-- a function consists of unit expression assignments "Map VarName Expr" and returns a single "TableExpr"
-- an assigment is identitified by the assigned variable, we assume the variables are not reused
-- each assignment maps a variable to an expression
data Function
  = F (M.Map VarName Expr) TableExpr
  deriving (Show)

------------------------------------------------
---- Executing public parts of an SQL query ----
------------------------------------------------

-- finds a cross product of N lists, applies the operation 'f' to elements that come together
crossProduct :: (a -> a -> a) -> [a] -> [[a]] -> [a]
crossProduct f start = foldr (\xs ys -> [f x y | x <- xs, y <- ys]) start

tableJoin :: [B.Table] -> B.Table
tableJoin xs = crossProduct (++) [[]] xs

vectorJoin :: [[[a]]] -> [[a]]
vectorJoin xss = crossProduct (++) [[]] xss

charVecJoin :: [[Bool]] -> [Bool]
charVecJoin xs = crossProduct (||) [False] xs

-- applies the list of filters to a table (computes AND of all filters for each row)
-- if all variables that are used in the filter are non-sensitive, apply the filter directly
-- if at least one variable is sensitive, use a sigmoid or something similar, it depends on the filter and the aggregating function
applyFilters :: [Bool]-> [Function] -> [[Int]] -> [Function] -> [S.Set B.Var] -> [[Double]] -> ([Function],[Bool])
applyFilters bs queries _             [] [] [] = (queries, bs)
applyFilters bs queries sensRowMatrix (filt:filts) (fvar:fvars) (fcol:fcols) =

    let tag = show (length filts) ++ "~" in -- use this to ensure that we assing unique new variables to each filter
    let newQueries = map (rewriteQuery filt tag fvar) queries in
    let goodRows = markGoodRows sensRowMatrix filt fvar fcol in

    --trace ("\n---L: " ++ show fvar ++ "\n" ++ show filt) $
    --apply the rest of the filters, take AND of row goodness for each row
    let newBs = zipWith (&&) bs goodRows in
    applyFilters newBs newQueries sensRowMatrix filts fvars fcols

markGoodRows :: [[Int]] -> Function ->  S.Set B.Var -> [Double] -> [Bool]
markGoodRows sensRowMatrix (F _ filterAggr) fvar fcol =

    let fun = case filterAggr of
            Filt ord _ c    -> (\z -> (ord == compare z c))
            FiltNeg ord _ c -> (\z -> not (ord == compare z c))
            Filter _        -> (\z -> z > 0.5)
    in
    -- check if the filter "contains at least one sensitive var"
    -- if it does not, then we may publicly mark the rows that do satisfy the filter
    if (S.size fvar == 0) then  map fun fcol
    -- if it does, then we may still publicly mark the insensitive rows, i.e rows that only contain values -1
    else zipWith (\xs xvalue -> if length (filter (< 0) xs) == length xs then fun xvalue else True) sensRowMatrix fcol

rewriteQuery :: Function -> String ->  S.Set B.Var -> Function -> Function
rewriteQuery (F fas filterAggr) tag fvar query@(F as b) =

    -- check if the filter "contains at least one sensitive var"
    if (S.size fvar == 0) then query else

    --we will introduce some new temporary variables
    let z  = "z~"  ++ tag in
    let z0 = "z0~" ++ tag in
    let z1 = "z1~" ++ tag in
    let z2 = "z2~" ++ tag in

    let w0 = "w0~" ++ tag in
    let w1 = "w1~" ++ tag in

    let b1 = "b1~" ++ tag in
    let b2 = "b2~" ++ tag in

    -- let sigmoid default scaling factor be 0.1
    let a = 0.1 in

    -- some important constants
    let one       = "1" in
    let oneNeg    = "-1" in
    let oneVal    = Const   1.0  in
    let oneNegVal = Const (-1.0) in

    -- inf = max - min
    let inf        = "inf~" in
    let aggrMax    = "max~" in
    let aggrMin    = "min~" in
    let aggrMinNeg = "-min~" in

    let maxRef    = ARMax in
    let minRef    = ARMin in
    let infAs     = M.fromList [(inf, Sum [aggrMax, aggrMinNeg]), (aggrMinNeg, Prod [aggrMin, oneNeg]), (aggrMax, maxRef), (aggrMin, minRef)] in

    -- if the filter is a negation, we will need to replace all choices 'b' with '1 - b'
    let (b0,maybeord,x,c,asPos, asNeg) =
            case filterAggr of
                Filter x        -> (b0,Nothing, x,c, [(b2, Id b0)], [(b2, Sum [one, b1]),(b1, Prod [b0,oneNeg])])
                                   where b0 = x
                Filt ord x c    -> (b0,Just ord,x,c, [(b2, Id b0)], [(b2, Sum [one, b1]),(b1, Prod [b0,oneNeg])])
                                   where b0 = "b0~" ++ tag
                FiltNeg ord x c -> (b0,Just ord,x,c, [(b2, Sum [one, b1]),(b1, Prod [b0,oneNeg])], [(b2, Id b0)])
                                   where b0 = "b0~" ++ tag
                t               -> error $ error_filterExprConstr t
    in
    let as'' = case maybeord of
            Nothing  -> asPos
            Just ord -> case ord of
                       EQ -> (b0, Tauoid  a c x) : asPos
                       LT -> (b0, Sigmoid a c x) : asNeg
                       GT -> (b0, Sigmoid a c x) : asPos
    in
    let as' = M.fromList $ [(oneNeg, oneNegVal), (one, oneVal)] ++ as'' in
    case b of

        -- for counting, take the filter output and compute l1-norm of the results
        SelectCount y ->
                 let asRw = \xs -> M.union xs as' in
                 let bRw  = \x ->  SelectL 1.0 b2 in
                 F (M.union fas (asRw as)) (bRw b)

        -- for sum and L-norms, we just multiply the value by the filter output
        SelectSum y ->
                let asRw = \xs -> M.union xs $ M.union as' (M.fromList [(z, Prod [y,b2])]) in
                let bRw  = \x ->  SelectSum z in
                F (M.union fas (asRw as)) (bRw b)

        SelectL p y ->
                let asRw = \xs -> M.union xs $ M.union as' (M.fromList [(z, Prod [y,b2])]) in
                let bRw  = \x ->  SelectL p z in
                F (M.union fas (asRw as)) (bRw b)

        -- for product, take 1 + b*(y - 1), where b is the filter output, so the values that are filtered out become 1
        -- this is not good to be sigmoid-approximated since the error becomes too large with multiplication
        SelectProd y ->
                let asRw = \xs -> M.union xs $ M.union as' (M.fromList [(z, Sum [one, z0]), (z0, Prod [z1,b2]), (z1, Sum [y,oneNeg])]) in
                let bRw  = \x ->  SelectProd z in
                F (M.union fas (asRw as)) (bRw b)

        -- for min/max, add/subtract a large quantity from the values that are filtered out, so that they would be ignored
        SelectMax y ->
                let asRw = \xs -> M.union xs $ M.union as' $ M.union infAs (M.fromList [(z, Sum [z1,y]), (z1, Prod [w1,inf]), (w1, Sum [b2,oneNeg])]) in
                let bRw  = \x ->  SelectMax z in
                F (M.union fas (asRw as)) (bRw b)

        SelectMin y ->
                let asRw = \xs -> M.union xs $ M.union as' $ M.union infAs (M.fromList [(z, Sum [z1,y]), (z1, Prod [w1,inf]), (w1, Sum [one,w0]),(w0, Prod [b2,oneNeg])]) in
                let bRw  = \x ->  SelectMin z in
                F (M.union fas (asRw as)) (bRw b)

        _ -> error $ error_filterExprConstr filterAggr




