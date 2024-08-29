module Main where

import Parser

main :: IO ()
main = getLine >>= parser >>= print
