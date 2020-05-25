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

postulate Float : Type{Lvl.𝟎}
{-# BUILTIN FLOAT Float #-}

primitive
  primFloatToWord64          : Float → Word64
  primFloatEquality          : Float → Float → Bool
  primFloatLess              : Float → Float → Bool
  primFloatNumericalEquality : Float → Float → Bool
  primFloatNumericalLess     : Float → Float → Bool
  primNatToFloat             : ℕ → Float
  primFloatPlus              : Float → Float → Float
  primFloatMinus             : Float → Float → Float
  primFloatTimes             : Float → Float → Float
  primFloatNegate            : Float → Float
  primFloatDiv               : Float → Float → Float
  primFloatSqrt              : Float → Float
  -- primRound         : Float → Int
  -- primFloor         : Float → Int
  -- primCeiling       : Float → Int
  primExp                    : Float → Float
  primLog                    : Float → Float
  primSin                    : Float → Float
  primCos                    : Float → Float
  primTan                    : Float → Float
  primASin                   : Float → Float
  primACos                   : Float → Float
  primATan                   : Float → Float
  primATan2                  : Float → Float → Float
  primShowFloat              : Float → String
