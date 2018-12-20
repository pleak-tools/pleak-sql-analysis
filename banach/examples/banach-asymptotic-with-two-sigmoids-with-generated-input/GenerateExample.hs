import Control.Monad
import System.Environment
import System.Random
import Text.Printf

main = do
  putStrLn "c1 c2"
  args <- getArgs
  let numLines = read (args !! 0) :: Int
  let maxVal = read (args !! 1) :: Double
  rng <- getStdGen
  forM_ (zip [(1::Int)..] (map (* maxVal) $ take numLines (randoms rng :: [Double]))) $ \ (i,val) ->
    printf "%d %0.9f\n" i val
