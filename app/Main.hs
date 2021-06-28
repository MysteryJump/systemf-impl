module Main where

import Data.Function
import Untyped

main :: IO ()
main = fix execute

execute :: IO () -> IO ()
execute f = do
  line <- getLine
  eval line
  f
