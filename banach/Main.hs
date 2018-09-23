import Parser as P
import PreprocessQ as PQ
import Banach as B
import ProgramOptions
import PostprocessQ

import Control.Monad

main :: IO ()
main = do
  args <- getProgramOptions
  let debug = not (alternative args)
  if generateQueries args
    then do
      if policyAnalysis args
        then do
          ((plcMap,plcCost),attMap,dataPath,initialQuery,colNames,typeMap,taskMap,_,tableExprData) <- PQ.getBanachAnalyserInput debug True (inputFp1 args) (inputFp2 args) (inputFp3 args) (inputFp4 args)
          performPolicyAnalysis args dataPath (delimiter args) initialQuery colNames typeMap taskMap tableExprData plcCost plcMap attMap
        else do
          (_,attMap,dataPath,initialQuery,colNames,typeMap,taskMap,sensitiveVarList,tableExprData) <- PQ.getBanachAnalyserInput debug False (inputFp1 args) (inputFp2 args) (inputFp3 args) (inputFp4 args)
          performDPAnalysis args dataPath (delimiter args) initialQuery colNames typeMap taskMap sensitiveVarList tableExprData attMap

    else do
      (outputTableName,qr,table,taskMap,tableExprData,colNames) <- P.getBanachAnalyserInput debug (inputFp2 args)
      B.performAnalyses args table outputTableName qr taskMap tableExprData
