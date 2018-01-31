module Query where

import Debug.Trace
import Control.Monad (void)
import Data.Either
import Data.List
import Data.Map
import qualified Data.Set as S
import Data.Void

import qualified Banach as B
import Expr

-- the format of the query
--   "Function"         is the queried function itself (SELECT)
--   "[String]"         is the list of table names that are used in the query (FROM)
--   "[Filter VarName]" is the list of filters used in the query (WHERE)
data Query
  = P Function [String] [Filter VarName]
  deriving (Show)

-- we support only simplest filters now, these should be delegated to SQL engine anyway
data Filter a = ANY
    | VarConst Ordering a Double
    | VarVar Ordering a a
  deriving Show


-- transforms elements that are not on certain index positions, assumes that the indices are sorted
mapNotAtIndices :: (a -> a) -> [Int] -> [a] -> Int -> [a]
mapNotAtIndices f [] xs _ = Data.List.map f xs
mapNotAtIndices _ _ [] _ = error ("index out of bounds")
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
fromCharVec bs = fst (unzip $ Data.List.filter (\(x,y) -> y) (zip [0..length bs - 1] bs))

-- finds a cross product of N lists, applies the operation 'f' to elements that come together
crossProduct :: (a -> a -> a) -> [a] -> [[a]] -> [a]
crossProduct f start = Data.List.foldr (\xs ys -> [f x y | x <- xs, y <- ys]) start

tableJoin :: [B.Table] -> B.Table
tableJoin xs = crossProduct (++) [[]] xs

charVecJoin :: [[Bool]] -> [Bool]
charVecJoin xs = crossProduct (||) [False] xs

-- applies the list of filters to a table (computes AND of all filters)
-- if all variables that are used in the filter are non-sensitive, apply the filter directly
-- if at least one variable is sensitive, use a sigmoid or something similar, it depends on the filter and the aggregating function
applyFilters :: Function -> B.Table -> [Bool] -> (S.Set VarName) -> Map VarName Int -> [Filter VarName] -> (Function,([Bool],B.Table))
applyFilters query table sensitiveRows _ _ [] = (query, (sensitiveRows, table))
applyFilters query@(F as b) table sensitiveRows sensitiveVars inputVarMap (f:fs) =
    let tag = show (length fs) ++ "~" in -- use this to ensure that we assing unique new variables to each filter
    let aggrVar = "z" ++ tag in
    let sigmVar = "s" ++ tag in
    let a = 0.1 in -- let the default scaling factor be 0.1
    let (nq, (nf, nt)) = case f of
            ANY -> (query, (sensitiveRows, table))
            -- TODO review all these sigmoids
            -- let the default scaling factor be 0.1
            -- take -0.1 if want to flip the sigmoid horizontally
            VarConst ord x c ->
                    if S.member x sensitiveVars then
                            case b of
                                -- for counting, take the sigmoid output and compute l1-norm of the results
                                SelectCount y ->
                                    let a'  = case ord of {LT -> a; GT -> -a; EQ -> error err} in
                                    let as' = Data.Map.union as (Data.Map.fromList [(aggrVar, Sigmoid a' c x)]) in
                                    let b'  = SelectL 1.0 aggrVar in
                                    (F  as' b', (sensitiveRows, table))

                                -- TODO this works as far as the function values for each row are nonnegative, otherwise l1-norm does not work
                                -- TODO need to think out how to define "infinity", we cannot do it freely yet
                                SelectMin y ->
                                    let a'  = case ord of {LT -> a; GT -> -a; EQ -> error err} in
                                    let as' = Data.Map.union as (Data.Map.fromList [(aggrVar, L 1.0 [y,sigmVar]), (sigmVar, Sigmoid a c x)]) in
                                    let b'  = SelectMin aggrVar in
                                    (F  as' b', (sensitiveRows, table))

                                SelectMax y ->
                                    let a' = case ord of {LT -> -a; GT -> a; EQ -> error err} in
                                    let as' = Data.Map.union as (Data.Map.fromList [(aggrVar, L 1.0 [y,sigmVar]), (sigmVar, Sigmoid (-a) c x)]) in
                                    let b'  = SelectMin aggrVar in
                                    (F  as' b', (sensitiveRows, table))

                                _ -> error err
                     else (query, unzip $ Data.List.filter (\(_,row) -> ord == compare (row !! (inputVarMap ! x)) c) (zip sensitiveRows table))
                     where err = "filter on sensitive vars for relation" ++ show ord ++ " and aggregator " ++ show b ++ " has not been added yet."
            VarVar ord x y -> 
                     if S.member x sensitiveVars || S.member y sensitiveVars then error ("multivariate filter on sensitive vars has not been added yet")
                     else (query, unzip $ Data.List.filter (\(_,row) -> ord == compare (row !! (inputVarMap ! x)) (row !! (inputVarMap ! y))) (zip sensitiveRows table))

    --apply the rest of the filters
    in applyFilters nq nt nf sensitiveVars inputVarMap fs

