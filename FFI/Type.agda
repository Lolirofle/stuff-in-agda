module FFI.Type where

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}
