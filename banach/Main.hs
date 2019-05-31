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
          (outputTableName,plcMaps,attMap,dataPath,initialQuery,numOfoutputs,colNames,typeMap,taskMap,_,tableExprData,_,colTableCounts) <- PQ.getBanachAnalyserInput args (inputFp1 args) (inputFp2 args) (inputFp3 args) (inputFp4 args)
          performPolicyAnalysis args outputTableName dataPath (delimiter args) initialQuery numOfoutputs colNames typeMap taskMap tableExprData plcMaps attMap colTableCounts
        else do
          (outputTableName,_,attMap,dataPath,initialQuery,numOfoutputs,colNames,typeMap,taskMap,sensitiveVarList,tableExprData,tableGs,colTableCounts) <- PQ.getBanachAnalyserInput args (inputFp1 args) (inputFp2 args) (inputFp3 args) (inputFp4 args)
          performDPAnalysis args outputTableName dataPath (delimiter args) initialQuery numOfoutputs colNames typeMap taskMap sensitiveVarList tableExprData attMap tableGs colTableCounts

    else do
      (outputTableName,qr,table,taskMap,tableExprData,colNames) <- P.getBanachAnalyserInput debug (inputFp2 args)
      B.performAnalyses args table outputTableName qr taskMap tableExprData
