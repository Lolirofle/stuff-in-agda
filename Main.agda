{-# OPTIONS --sized-types --guardedness #-}

-- Note: This module is not meant to be imported.
module Main where

import Data
import Data.Boolean
import Data.List
import Data.List.Functions
import FFI.IO as FFI

main : FFI.IO Data.Unit
main = FFI.printStrLn("Okay")
