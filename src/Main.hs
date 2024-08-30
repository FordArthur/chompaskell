module Main where

import Parser

main :: IO ()
main = getLine >>= parser >>= either print (putStrLn . unlines . map show)
