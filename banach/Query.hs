module Query where

import Debug.Trace
import Control.Monad (void)
import Data.Either
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Void

import qualified Banach as B
import ErrorMsg
import Expr

-- the format of the query
--   String             is the name of the resulting table
--   "[String]"         is the list of names assigned to the resulting columns
--   "[Function]"       is the list of the queried function itself (SELECT)
--   "[String]"         is the list of table names that are used in the query (FROM)
--   "[Function]"       is the list of filters used in the query (WHERE)
data Query
  = P String [String] [Function] [String] [Function]
  deriving (Show)

-- a function consists of unit expression assignments "Map VarName Expr" and returns a single "TableExpr"
-- an assigment is identitified by the assigned variable, we assume the variables are not reused
-- each assignment maps a variable to an expression
data Function
  = F (M.Map VarName Expr) TableExpr
  deriving (Show)

-- transforms elements that are not on certain index positions, assumes that the indices are sorted
mapNotAtIndices :: (a -> a) -> [Int] -> [a] -> Int -> [a]
mapNotAtIndices f [] xs _ = map f xs
mapNotAtIndices _ _ [] _  = error (error_internal ++ "index out of bounds in function mapNotAtIndices")
mapNotAtIndices f is'@(i:is) (x:xs) k =
    if (i == k) then x:(mapNotAtIndices f is xs (k+1))
    else (f x):(mapNotAtIndices f is' xs (k+1))

------------------------------------------------
---- Executing public parts of an SQL query ----
------------------------------------------------

-- characteristic vector of a vector of indices, bounded by n
charVec :: Int -> [Int] -> [Bool]
charVec n indices = mapNotAtIndices (\x -> False) indices (replicate n True) 0

fromCharVec :: [Bool] -> [Int]
fromCharVec bs = fst $ unzip $ filter (\(x,y) -> y) (zip [0..length bs - 1] bs)

-- finds a cross product of N lists, applies the operation 'f' to elements that come together
crossProduct :: (a -> a -> a) -> [a] -> [[a]] -> [a]
crossProduct f start = foldr (\xs ys -> [f x y | x <- xs, y <- ys]) start

tableJoin :: [B.Table] -> B.Table
tableJoin xs = crossProduct (++) [[]] xs

vectorJoin :: [[[a]]] -> [[a]]
vectorJoin xss = crossProduct (++) [[]] xss

charVecJoin :: [[Bool]] -> [Bool]
charVecJoin xs = crossProduct (||) [False] xs

-- applies the list of filters to a table (computes AND of all filters)
-- if all variables that are used in the filter are non-sensitive, apply the filter directly
-- if at least one variable is sensitive, use a sigmoid or something similar, it depends on the filter and the aggregating function
applyFilters :: Double -> [Function] -> B.Table -> [a] -> M.Map VarName Int -> [Function] -> [[B.Var]] -> [[Double]] -> ([Function],([a],B.Table))
applyFilters _ queries table sensitiveRows _ [] [] [] = (queries, (sensitiveRows, table))
applyFilters infVal queries table sensitiveRows inputVarMap (f:fs) (fvar:fvars) (fcol:fcols) =

    let tag = show (length fs) ++ "~" in -- use this to ensure that we assing unique new variables to each filter
    let nq       = map (rewriteQuery f infVal tag fvar) queries in
    let (nf, nt) = rewriteTable f inputVarMap sensitiveRows fvar table fcol in

    --apply the rest of the filters
    applyFilters infVal nq nt nf inputVarMap fs fvars fcols

rewriteTable :: Function -> M.Map VarName Int -> [a] -> [B.Var] -> B.Table -> [Double] -> ([a], B.Table)
rewriteTable (F _ (Filt ord x c)) inputVarMap sensitiveRows fvar table fcol =

    -- check if the filter "contains at least one sensitive var"
    -- if it does not, then we remove the rows not satisfying the filter immediately
    if (length fvar > 0) then (sensitiveRows, table)
    else 
        let (zs1,zs2,_) = unzip3 $ filter (\(y,z,xvalue) -> (ord == compare xvalue c)) (zip3 sensitiveRows table fcol) in
        (zs1, zs2)

rewriteQuery :: Function -> Double -> String -> [B.Var] -> Function -> Function
rewriteQuery (F fas (Filt ord x c)) infVal tag fvar query@(F as b) =

    --we will introduce some new temporary variables
    let z  = "z~"  ++ tag in
    let z0 = "z0~" ++ tag in
    let z1 = "z1~" ++ tag in
    let z2 = "z2~" ++ tag in

    -- let the default scaling factor be 0.1
    let a = 0.1 in

    -- some important constants
    let infPos    = "inf" in
    let infNeg    = "-inf" in
    let infPosVal = Const ( 1.0 * infVal) in
    let infNegVal = Const (-1.0 * infVal) in

    let one       = "1" in
    let oneNeg    = "-1" in
    let oneVal    = Const   1.0  in
    let oneNegVal = Const (-1.0) in

    let two       = "2" in
    let twoVal    = Const   2.0  in

    -- check if the filter "contains at least one sensitive var"
    if (length fvar > 0) then

            case b of

                -- for counting, take the sigmoid output and compute l1-norm of the results
                SelectCount y ->
                     let a'  = case ord of {LT -> -a; GT -> a; EQ -> error err} in
                     let asRw = \xs -> M.union xs (M.fromList [(z, Sigmoid a' c x)]) in
                     let bRw  = \x ->  SelectL 1.0 z in
                     F (M.union fas (asRw as)) (bRw b)

                -- for sum and L-norms, we just multiply the value by the sigmoid output
                SelectSum y ->
                    let a' = case ord of {LT -> -a; GT -> a; EQ -> error err} in
                    let asRw = \xs -> M.union xs (M.fromList [(z, Prod [y,z1]), (z1, Sigmoid a' c x)]) in
                    let bRw  = \x ->  SelectSum z in
                    F (M.union fas (asRw as)) (bRw b)

                SelectL p y ->
                    let a' = case ord of {LT -> -a;  GT -> a; EQ -> error err} in
                    let asRw = \xs -> M.union xs (M.fromList [(z, Prod [y,z1]), (z1, Sigmoid a' c x)]) in
                    let bRw  = \x ->  SelectL p z in
                    F (M.union fas (asRw as)) (bRw b)

                -- for product, we take 1 + b*(y - 1), where b is the sigmoid output, so the values that are filtered out become 1
                -- this is not good to be sigmoid-approximated since the error becomes too large with multiplication
                SelectProd y ->
                    let a' = case ord of {LT -> -a; GT -> a; EQ -> error err} in
                    let asRw = \xs -> M.union xs (M.fromList [(z, Sum [one, z0]), (z0, Prod [z1,z2]), (z1, Sum [y,oneNeg]), (z2, Sigmoid a' c x),
                                                              (oneNeg, oneNegVal), (one, oneVal)]) in
                    let bRw  = \x ->  SelectProd z in
                    F (M.union fas (asRw as)) (bRw b)

                -- for min/max, could we add/subtract a large quantity from the values that are filtered out, so that they would be ignored
                -- this does not work well since if the quantity does not depend on the input, it may be too large
                -- take 'min(y, 2b*inf - inf)' for SelectMax, and 'max(y, 2b*inf - inf)' for SelectMin, where b is flipped for SelectMin
                SelectMax y ->
                    let a' = case ord of {LT -> -a;  GT -> a; EQ -> error err} in
                    let asRw = \xs -> M.union xs (M.fromList [(z, Min [y,z0]), (z0, Sum [z1,infNeg]), (z1, Prod [two,z2,infPos]), (z2, Sigmoid a' c x),
                                                              (infNeg, infNegVal), (infPos, infPosVal), (two, twoVal)]) in
                    let bRw  = \x ->  SelectMax z in
                    F (M.union fas (asRw as)) (bRw b)

                SelectMin y ->
                    let a'  = case ord of {LT -> a; GT -> -a; EQ -> error err} in
                    let asRw = \xs -> M.union xs (M.fromList [(z, Max [y,z0]), (z0, Sum [z1,infNeg]), (z1, Prod [two,z2,infPos]), (z2, Sigmoid a' c x),
                                                              (infNeg, infNegVal), (infPos, infPosVal), (two, twoVal)]) in
                    let bRw  = \x ->  SelectMin z in
                    F (M.union fas (asRw as)) (bRw b)

                -- TODO currently, max supports filters only if they are computed over positive values
                -- similarly to sum, we may just multiply the value by the sigmoid output in this case to compute max
                --SelectMax y ->
                --    let a' = case ord of {LT -> -a; GT -> a; EQ -> error err} in
                --    let asRw = \xs -> M.union xs (M.fromList [(z, Prod [y,z1]), (z1, Sigmoid a' c x)]) in
                --    let bRw  = \x ->  SelectMax z in
                --    F (M.union fas (asRw as)) (bRw b)

                -- for min, we first transform x to exp^{-x} and then find the maximum
                -- this assumes that in the end "ln" should be applied in the end, but sensitivity remains the same
                -- TODO the analyser should probably assume that y >= 0, otherwise we get infinite sensitivity
                -- SelectMin y ->
                --    let a'  = case ord of {LT -> a; GT -> -a; EQ -> error err} in
                --    let asRw = \xs -> M.union xs (M.fromList [(z0, Exp (-1.0) y), (z, Prod [z0,z1]), (z1, Sigmoid a' c x)]) in
                --    let bRw  = \x ->  SelectMax z in
                --    F (M.union fas (asRw as)) (bRw b)

                _ -> error err
    else query
    where err = error_filterExpr ++ ": filter for sensitive vars, relation " ++ show ord ++ " and aggregator " ++ show b ++ " has not been added yet."



