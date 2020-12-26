{-# OPTIONS --sized-types --guardedness #-}

-- Note: This module is not meant to be imported.
module Js where

import Data
import Data.Boolean
import FFI.IO as FFI

main : FFI.IO Data.Unit
main = FFI.printStrLn("Okay")
