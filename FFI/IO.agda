module FFI.IO where

import      Lvl
open import Data
open import String

postulate IO : ∀{a} → Set a → Set a
{-# BUILTIN IO IO #-}
{-# FOREIGN GHC type AgdaIO a b = IO b #-}
{-# COMPILE GHC IO = type AgdaIO #-}

{-# FOREIGN GHC import qualified Data.Text.IO #-}

postulate printStr : String → IO(Unit{Lvl.𝟎})
{-# COMPILE GHC printStr = Data.Text.IO.putStr #-}

postulate printStrLn : String → IO(Unit{Lvl.𝟎})
{-# COMPILE GHC printStrLn = Data.Text.IO.putStrLn #-}
