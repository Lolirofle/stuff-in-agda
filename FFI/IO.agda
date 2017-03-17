module FFI.IO where

open import FFI.Type
open import String

postulate IO : ∀{a} → Set a → Set a
{-# BUILTIN IO IO #-}
{-# HASKELL type AgdaIO a b = IO b #-}
{-# COMPILED_TYPE IO AgdaIO #-}

postulate
  printStr   : String → IO Unit
  printStrLn : String → IO Unit

{-# COMPILED printStr   putStr   #-}
{-# COMPILED printStrLn putStrLn #-}
