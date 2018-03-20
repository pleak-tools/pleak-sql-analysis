import Parser as P
import Banach as B
import ProgramOptions

main :: IO ()
main = do
  args <- getProgramOptions
  let debug = not (alternative args)
  (outputTableName,table,taskMap,tableExprData) <- P.getBanachAnalyserInput debug (inputFp args)
  B.performAnalyses args table outputTableName taskMap tableExprData
