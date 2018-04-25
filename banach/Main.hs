import Parser as P
import Banach as B
import BanachQ as BQ
import ProgramOptions

import Control.Monad

main :: IO ()
main = do
  args <- getProgramOptions
  let debug = not (alternative args)
  (outputTableName,qr,table,taskMap,tableExprData,colNames) <- P.getBanachAnalyserInput debug (inputFp args)
  B.performAnalyses args table outputTableName qr taskMap tableExprData
  when debug $ putStrLn "================================="
  when debug $ putStrLn "Generating SQL queries for computing the analysis results:"
  when debug $ BQ.performAnalyses args colNames outputTableName qr taskMap tableExprData
