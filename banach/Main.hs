import Parser as P
import PreprocessQ as PQ
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
      BQ.performAnalyses args colNames tableExprData
    else do
      (outputTableName,qr,table,taskMap,tableExprData,colNames) <- P.getBanachAnalyserInput debug (inputFp args)
      B.performAnalyses args table outputTableName qr taskMap tableExprData
