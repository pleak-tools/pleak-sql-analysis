import Parser as P
import ParserQ as PQ
import Banach as B
import BanachQ as BQ
import ProgramOptions

import Control.Monad

main :: IO ()
main = do
  args <- getProgramOptions
  let debug = not (alternative args)
  if generateQueries args
    then do
      (colNames,tableExprData) <- PQ.getBanachAnalyserInput debug (inputFp args)
      when debug $ putStrLn "================================="
      when debug $ putStrLn "Generating SQL queries for computing the analysis results:"
      BQ.performAnalyses args colNames tableExprData
    else do
      (outputTableName,qr,table,taskMap,tableExprData,colNames) <- P.getBanachAnalyserInput debug (inputFp args)
      B.performAnalyses args table outputTableName qr taskMap tableExprData
