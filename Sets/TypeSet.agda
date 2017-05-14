module Sets.TypeSet {l₁} {l₂} where

import      Level as Lvl
open import Data
open import Functional
open import Logic.Propositional{Lvl.𝐒(l₁) Lvl.⊔ l₂}
open import Logic.Predicate{Lvl.𝐒(l₁)}{l₂}
open import Type

data TSet : Type{Lvl.𝐒(l₁)} where
  set : Set(l₁) → TSet

set-of : TSet → Set(l₁)
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
