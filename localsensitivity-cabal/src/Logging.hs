module Logging (red, green, yellow, warn, fatal, err, ice) where

--import GHC.Stack (HasCallStack, withFrozenCallStack)
import System.Exit
import System.IO

red :: String -> String
red s = "\x1b[31m" ++ s ++ "\x1b[0m"

green :: String -> String
green s = "\x1b[32m" ++ s ++ "\x1b[0m"

yellow :: String -> String
yellow s = "\x1b[33m" ++ s ++ "\x1b[0m"

-- green :: String -> String
-- green s = "\x1b[32m" ++ s ++ "\x1b[0m"

-------------------------------
-- Basic logging on IO monad --
-------------------------------

-- ^ Report warning.
warn :: String -> IO ()
warn msg = hPutStrLn stderr $ yellow $ "[WARN] " ++ msg

-- ^ Report error and exit. Unrecoverable.
fatal :: String -> IO a
fatal msg = die $ red $ "[FATAL] " ++ msg

-- ^ Report error.
err :: String -> IO ()
err msg = hPutStrLn stderr $ red $ "[ERROR] " ++ msg

-- ^ Internal compile error.
--ice :: HasCallStack => String -> a
--ice msg = withFrozenCallStack error $ red $ "[ICE] " ++ msg
ice :: String -> a
ice msg = error $ red $ "[ICE] " ++ msg
