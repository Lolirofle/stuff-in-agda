module MachineWord where

import      Lvl
open import Data.Boolean
open import Numeral.Natural
open import String
open import Syntax.Number
open import Type

postulate Word64 : Type{Lvl.𝟎}
{-# BUILTIN WORD64 Word64 #-}

private
  module Primitives where
    primitive primWord64ToNat   : Word64 → ℕ
    primitive primWord64FromNat : ℕ → Word64

module Word64 where
  open Primitives renaming
    ( primWord64ToNat   to toℕ
    ; primWord64FromNat to fromℕ
    ) public

  instance
    Word64-infiniteNumeral : InfiniteNumeral(Word64)
    Word64-infiniteNumeral = InfiniteNumeral.intro fromℕ
