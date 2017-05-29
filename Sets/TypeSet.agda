module Sets.TypeSet {ℓ₁} {ℓ₂} where

import      Level as Lvl
open import Data
open import Functional
open import Logic.Propositional{Lvl.𝐒(ℓ₁) Lvl.⊔ ℓ₂}
open import Logic.Predicate{Lvl.𝐒(ℓ₁)}{ℓ₂}
open import Type

data TSet : Type{Lvl.𝐒(ℓ₁)} where
  set : Set(ℓ₁) → TSet

set-of : TSet → Set(ℓ₁)
set-of (set s) = s

-- _∋_ : (S : TSet) → set-of(S) → Stmt
-- _∋_ _ _ = ⊤

-- _⊇_ : TSet → TSet → Stmt
-- _⊇_ A B = (∀{x} → ((A ∋ x) → (B ∋ x)))

∅ : TSet
∅ = set(Empty)

_∪_ : TSet → TSet → TSet
_∪_ (set A) (set B) = set(A ‖ B)

_∩_ : TSet → TSet → TSet
_∩_ (set A) (set B) = set(A ⨯ B)
