module String.Functions where

open import Char
open import Data.Boolean
open import Data.List
import      Data.List.Functions as List
open import Data.Option
import      Data.Option.Functions as Option
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional as Fn
open import Numeral.Natural
import      Numeral.Natural.Oper as ℕ
open import String
open import Type.Dependent

module Primitives where
  primitive primStringUncons   : String → Option(Σ Char (const String))
  primitive primStringToList   : String → List(Char)
  primitive primStringFromList : List(Char) → String
  primitive primStringAppend   : String → String → String
  primitive primStringEquality : String → String → Bool

open Primitives renaming
  ( primStringToList   to chars
  ; primStringFromList to fromChars
  ; primStringAppend   to _++_
  ; primStringEquality to _==_
  ) public

splitFirst : String → Option(Char ⨯ String)
splitFirst = Option.map (\(intro c s) → (c , s)) ∘ Primitives.primStringUncons

first : String → Option(Char)
first = Option.map Σ.left ∘ Primitives.primStringUncons

tail : String → Option(String)
tail = Option.map Σ.right ∘ Primitives.primStringUncons

tail₀ : String → String
tail₀ = Fn.swap(Option._or_) "" ∘ tail

length : String → ℕ
length = List.length ∘ chars

repeat : Char → ℕ → String
repeat = fromChars ∘₂ List.repeat

padLeft : Char → ℕ → String → String
padLeft c n str = repeat c (n ℕ.−₀ length(str)) ++ str

padRight : Char → ℕ → String → String
padRight c n str = str ++ repeat c (n ℕ.−₀ length(str))
