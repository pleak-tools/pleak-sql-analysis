import Database.HsSqlPpp.Parse
import System.Environment
import System.Exit

import qualified Data.Text.Lazy.IO as T

main :: IO ()
main = do
  args <- getArgs
  case args of
    [f] -> do
      src <- T.readFile f
      let ast = parseStatements defaultParseFlags f Nothing src
      print ast
    _ -> die "Invalid program arguments. Expecting a file containing SQL statements."
