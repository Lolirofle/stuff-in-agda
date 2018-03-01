-- Sets represented by unary predicates (Like restricted comprehension)
module Sets.PredicateSet {ℓ₁} {ℓ₂} where

import Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Propositional.Theorems{ℓ₁ Lvl.⊔ ℓ₂} using ([↔]-transitivity)
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂} renaming (_≡_ to _[≡]_ ; _≢_ to _[≢]_)
open import Type{ℓ₂}

-- A set
PredSet : Type → Set(Lvl.𝐒(ℓ₁ Lvl.⊔ ℓ₂))
PredSet(T) = (T → Stmt)

-- The statement of whether an element is in a set
_∈_ : ∀{T} → T → PredSet(T) → Stmt
_∈_ = apply

_∉_ : ∀{T} → T → PredSet(T) → Stmt
_∉_ x S = ¬(x ∈ S)

_∋_ : ∀{T} → PredSet(T) → T → Stmt
_∋_ S x = (x ∈ S)

_∌_ : ∀{T} → PredSet(T) → T → Stmt
_∌_ S x = ¬(S ∋ x)

-- An empty set
∅ : ∀{T} → PredSet(T)
∅ = const(⊥)

-- An universal set
𝐔 : ∀{T} → PredSet(T)
𝐔 = const(⊤)

-- A singleton set (a set with only one element)
singleton : ∀{T} → T → PredSet(T)
singleton = _[≡]_

-- A statement of whether a set is a subset of a set
_⊆_ : ∀{T} → PredSet(T) → PredSet(T) → Stmt
_⊆_ S₁ S₂ = (∀{x} → (x ∈ S₁) → (x ∈ S₂))

-- A statement of whether a set is a superset of a set
_⊇_ : ∀{T} → PredSet(T) → PredSet(T) → Stmt
_⊇_ S₁ S₂ = (∀{x} → (x ∈ S₁) ← (x ∈ S₂))

-- A statement of whether a set is equivalent to a set
_≡_ : ∀{T} → PredSet(T) → PredSet(T) → Stmt
_≡_ S₁ S₂ = (∀{x} → (x ∈ S₁) ↔ (x ∈ S₂))

-- An union of two sets
_∪_ : ∀{T} → PredSet(T) → PredSet(T) → PredSet(T)
_∪_ S₁ S₂ x = (S₁(x) ∨ S₂(x))

-- An intersection of two sets
_∩_ : ∀{T} → PredSet(T) → PredSet(T) → PredSet(T)
_∩_ S₁ S₂ x = (S₁(x) ∧ S₂(x))

-- A complement of a set
∁_ : ∀{T} → PredSet(T) → PredSet(T)
∁_ S x = (¬ S(x))

{- TODO: Levels
℘_ : ∀{T} → PredSet(T) → PredSet(PredSet(T))
℘_ S x = (x ⊆ S)

_⋃_ : ∀{T} → PredSet(PredSet(T)) → PredSet(T)
_⋃_ S x = ∃(s ↦ (s ∈ S) ∧ (x ∈ s))

_⋂_ : ∀{T} → PredSet(PredSet(T)) → PredSet(T)
_⋂_ S x = (∀{s} → (s ∈ S) → (x ∈ s))
-}
