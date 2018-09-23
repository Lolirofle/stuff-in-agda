module String where

import      Lvl
open import Data.List
open import Type{Lvl.𝟎}

{-# BUILTIN CHAR Char #-}

{-# BUILTIN STRING String #-}

primitive
  primStringToList   : String → List(Char)
  primStringFromList : List(Char) → String
  primStringAppend   : String → String → String
