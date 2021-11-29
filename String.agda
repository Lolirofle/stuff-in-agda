module String where

import      Lvl
open import Type

postulate String : Type{Lvl.𝟎}
{-# BUILTIN STRING String #-}

module _ {ℓ} (T : Type{ℓ}) where
  -- StringRepr(T) means that the type T have a standard representation as a string (not necessarily an unique or parser-friendly one) used for pretty-printing.
  record StringRepr : Type{ℓ} where
    field string : T → String
  open StringRepr ⦃ … ⦄ public

private
  module Primitives where
    primitive primShowString : String → String

instance
  String-stringRepr : StringRepr(String)
  StringRepr.string String-stringRepr = Primitives.primShowString
