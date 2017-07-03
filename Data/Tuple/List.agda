module Data.Tuple.List{ℓ} where

import      Level as Lvl
open import Data using (Unit ; <>)
open        Data.Tuple
import      List
open        List using (List)
open import Type{ℓ}

-- Tuple type described with lists
Tuple : List(Type) → Type
Tuple(List.∅)          = Unit
Tuple(T List.⊰ List.∅) = T
Tuple(T List.⊰ L)      = (T ⨯ Tuple(L))

pattern ∅        = <>
pattern _⊰∅ a    = a
pattern _⊰+_ a l = (a , l)

_⊰_ : ∀{T}{L} → T → Tuple(L) → Tuple(T List.⊰ L)
_⊰_ {_}{List.∅}     a _ = a
_⊰_ {_}{_ List.⊰ _} a l = (a , l)

head : ∀{T}{L} → Tuple(T List.⊰ L) → T
head{_}{List.∅}    (a ⊰∅)   = a
head{_}{_ List.⊰ _}(a ⊰+ _) = a

tail : ∀{T}{L} → Tuple(T List.⊰ L) → Tuple(L)
tail{_}{List.∅}    (_ ⊰∅)   = ∅
tail{_}{_ List.⊰ _}(_ ⊰+ l) = l

module _ where
  open import List.Properties
  open import Relator.Equals

  _++_ : ∀{L₁ L₂} → Tuple(L₁) → Tuple(L₂) → Tuple(L₁ List.++ L₂)
  _++_{L}                   {List.∅} (l)(_)         = [≡]-substitutionₗ {Lvl.𝟎}{_}{_}{_}{_}{L} ([++]-identityᵣ) {Tuple} (l)
  _++_{List.∅}              {_}      (_)(l)         = l
  _++_{A List.⊰ List.∅}     {L₂}     (a ⊰∅)   (l₂) = _⊰_ {A}{L₂} (a) (l₂)
  _++_{A List.⊰ B List.⊰ L₁}{L₂}     (a ⊰+ l₁)(l₂) = _⊰_ {A}{(B List.⊰ L₁) List.++ L₂} (a) (_++_ {B List.⊰ L₁}{L₂} l₁ l₂)

module _ where
  open import Numeral.Natural

  length : ∀{L} → Tuple(L) → ℕ
  length{L} (_) = List.length(L)

module Theorems where
  -- TupleRaise : Tuple(repeat(n)(T)) ≡ T ^ n
