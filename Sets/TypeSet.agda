-- TODO: This is the same idea as PredicateSet
module Sets.TypeSet {ℓ₁} {ℓ₂} where

import      Lvl
open import Data
open import Functional
open import Logic.Propositional{Lvl.𝐒(ℓ₁) Lvl.⊔ ℓ₂}
open import Logic.Predicate{Lvl.𝐒(ℓ₁)}{ℓ₂}
open import Type

record TypeSet(T : Set) : Set₁ where
  field
    inclusion-fn : T → Set
open TypeSet

-- _∋_ : (S : TypeSet) → set-of(S) → Stmt
-- _∋_ _ _ = ⊤

-- _⊇_ : TypeSet → TypeSet → Stmt
-- _⊇_ A B = (∀{x} → ((A ∋ x) → (B ∋ x)))

∅ : ∀{T} → TypeSet(T)
∅ = record{inclusion-fn = const Empty}

{-
_∪_ : ∀{T} → TypeSet(T) → TypeSet(T) → TypeSet(T)
_∪_ A B = record{inclusion-fn = inclusion-fn(A) ‖ inclusion-fn(B)}

_∩_ : ∀{T} → TypeSet(T) → TypeSet(T) → TypeSet(T)
_∩_ A B = record{inclusion-fn = inclusion-fn(A) ⨯ inclusion-fn(B)}
-}
