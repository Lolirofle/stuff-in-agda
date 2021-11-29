module Char.Functions where

open import Char
open import Data.Boolean
open import Numeral.Natural
open import String

private
  module Primitives where
    primitive primShowChar     : Char → String
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

open Primitives renaming
  ( primIsLower      to isLower
  ; primIsDigit      to isDigit
  ; primIsAlpha      to isAlphabetic
  ; primIsSpace      to isSpace
  ; primIsAscii      to isAscii
  ; primIsLatin1     to isLatin1
  ; primIsPrint      to isPrint
  ; primIsHexDigit   to isHexDigit
  ; primToUpper      to toUppercase
  ; primToLower      to toLowercase
  ; primCharToNat    to unicodeCodePoint
  ; primNatToChar    to fromUnicodeCodePoint
  ; primCharEquality to _≡?_
  ) public

instance
  Char-stringRepr : StringRepr(Char)
  StringRepr.string Char-stringRepr = Primitives.primShowChar
