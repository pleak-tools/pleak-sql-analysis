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
      (dataPath,initialQuery,colNames,typeMap,taskMap,tableExprData) <- PQ.getBanachAnalyserInput debug (inputFp1 args) (inputFp2 args)
      BQ.performAnalyses args dataPath initialQuery colNames typeMap taskMap tableExprData
    else do
      (outputTableName,qr,table,taskMap,tableExprData,colNames) <- P.getBanachAnalyserInput debug (inputFp2 args)
      B.performAnalyses args table outputTableName qr taskMap tableExprData
