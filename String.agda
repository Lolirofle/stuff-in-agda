module String where

import      Lvl
open import Data.Boolean
open import Data.List
open import Numeral.Natural
open import Type

postulate Char : Type{Lvl.𝟎}
{-# BUILTIN CHAR Char #-}

postulate String : Type{Lvl.𝟎}
{-# BUILTIN STRING String #-}

private
  module Primitives where
    primitive primStringToList   : String → List(Char)
    primitive primStringFromList : List(Char) → String
    primitive primStringAppend   : String → String → String
    primitive primStringEquality : String → String → Bool
    primitive primShowChar       : Char → String
    primitive primShowString     : String → String
    primitive primShowNat        : ℕ → String

    primitive primIsLower      : Char → Bool
    primitive primIsDigit      : Char → Bool
    primitive primIsAlpha      : Char → Bool
    primitive primIsSpace      : Char → Bool
    primitive primIsAscii      : Char → Bool
    primitive primIsLatin1     : Char → Bool
    primitive primIsPrint      : Char → Bool
    primitive primIsHexDigit   : Char → Bool
    primitive primToUpper      : Char → Char
    primitive primToLower      : Char → Char
    primitive primCharToNat    : Char → ℕ
    primitive primNatToChar    : ℕ → Char
    primitive primCharEquality : Char → Char → Bool

module String where
  open Primitives renaming
    ( primStringToList   to toList
    ; primStringFromList to fromList
    ; primStringAppend   to _++_
    ; primStringEquality to _==_
    ; primShowChar       to fromChar
    ; primShowNat        to fromℕ
    ) public

  {-
  open import Relator.Equals
  open import Relator.Equals.Proofs
  open import Syntax.Transitivity

  primitive primEraseEquality : ∀{ℓ}{A : Type{ℓ}}{x y : A} → (x ≡ y) → (x ≡ y)

  unsafeDefinitionalEquality : ∀{ℓ}{A : Type{ℓ}}{x y : A} → (x ≡ y)
  unsafeDefinitionalEquality {x = x}{y = y} = primEraseEquality xy where
    postulate xy : x ≡ y

  toList-fromList-of-[⊰] : ∀{x}{l} → (toList(fromList(x ⊰ l)) ≡ x ⊰ toList(fromList(l)))
  toList-fromList-of-[⊰] = unsafeDefinitionalEquality

  fromList-toList-inverse : ∀{s} → (fromList(toList(s)) ≡ s)
  fromList-toList-inverse = unsafeDefinitionalEquality

  toList-fromList-inverse : ∀{l} → (toList(fromList(l)) ≡ l)
  toList-fromList-inverse {∅}     = [≡]-intro
  toList-fromList-inverse {x ⊰ l} = toList-fromList-of-[⊰] 🝖 [≡]-with(x ⊰_) (toList-fromList-inverse {l})
  -}
