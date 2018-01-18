import Parser as P
import Banach as B
import ProgramOptions

main :: IO ()
main = do
  args <- getProgramOptions
  (table,expr) <- P.getBanachAnalyserInput (inputFp args)
  B.performAnalysis args table expr
