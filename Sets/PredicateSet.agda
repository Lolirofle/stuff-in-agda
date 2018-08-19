-- Sets represented by unary predicates (Like restricted comprehension)
-- Similiar to BoolSet, but instead using the builtin constructive logic with levels.
module Sets.PredicateSet where

import      Lvl
open import Functional
import      Logic.Propositional
import      Logic.Propositional.Theorems
import      Logic.Predicate
import      Relator.Equals
import      Type

module _ {ℓₗ}{ℓₒ} where
  open Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ}
  open Logic.Propositional.Theorems{ℓₗ Lvl.⊔ ℓₒ} using ([↔]-transitivity)
  open Logic.Predicate{ℓₗ}{ℓₒ}
  open Relator.Equals{ℓₗ Lvl.⊔ ℓₒ}
  open Type{ℓₒ}

  -- A set
  -- Note: It is only within a certain type, so everything Pred{T} is actually a subset of T if T were a set.
  PredSet : Type → Set(Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ))
  PredSet(T) = (T → Stmt)

  -- The statement of whether an element is in a set
  -- TODO: Maybe define this using a equivalence relation instead? (Alternatively a Setoid: x ∈ S = ∃(y ↦ (x ≡_T y) ∧ S(y)))
  _∈_ : ∀{T} → T → PredSet(T) → Stmt
  _∈_ = apply -- (x ∈ S) = S(x)

  _∉_ : ∀{T} → T → PredSet(T) → Stmt
  _∉_ = (¬_) ∘₂ (_∈_) -- (x ∉ S) = ¬(x ∈ S)

  _∋_ : ∀{T} → PredSet(T) → T → Stmt
  _∋_ = swap(_∈_) -- (S ∋ x) = (x ∈ S)

  _∌_ : ∀{T} → PredSet(T) → T → Stmt
  _∌_ = (¬_) ∘₂ (_∋_) -- (S ∌ x) = ¬(S ∋ x)

  -- An empty set
  ∅ : ∀{T} → PredSet(T)
  ∅ = const(⊥)

  -- An universal set
  -- Note: It is only within a certain type, so 𝐔{T} is actually a subset of everything. It is the subset containing only T if T were a set.
  𝐔 : ∀{T} → PredSet(T)
  𝐔 = const(⊤)

  -- A singleton set (a set with only one element)
  •_ : ∀{T} → T → PredSet(T)
  •_ = (_≡_)

  -- An union of two sets
  _∪_ : ∀{T} → PredSet(T) → PredSet(T) → PredSet(T)
  _∪_ S₁ S₂ x = (S₁(x) ∨ S₂(x))

  -- An intersection of two sets
  _∩_ : ∀{T} → PredSet(T) → PredSet(T) → PredSet(T)
  _∩_ S₁ S₂ x = (S₁(x) ∧ S₂(x))

  -- A complement of a set
  ∁_ : ∀{T} → PredSet(T) → PredSet(T)
  ∁_ = (¬_) ∘_ -- ∁_ S x = (¬ S(x))

  _∖_ : ∀{T} → PredSet(T) → PredSet(T) → PredSet(T)
  _∖_ S₁ S₂ = (S₁ ∩ (∁ S₂))

  module _ where
    open import Data.Boolean
    open import Functional.Proofs
    open import Structure.Function.Domain{ℓₗ}

    map : ∀{A B} → (f : A → B) → ⦃ _ : Bijective{ℓₒ}(f) ⦄ → PredSet(A) → PredSet(B)
    map f S x = S(inv-fn(f)(x))

    filter : ∀{T} → (T → Bool) → PredSet(T) → PredSet(T)
    filter f S x = (S(x) ∧ (f(x) ≡ 𝑇))

module _ {ℓₗ₁}{ℓₗ₂} {ℓₒ} where
  open Logic.Propositional

  -- A statement of whether a set is a subset of a set
  _⊆_ : ∀{T} → PredSet{ℓₗ₁}{ℓₒ}(T) → PredSet{ℓₗ₂}{ℓₒ}(T) → Stmt{ℓₗ₁ Lvl.⊔ ℓₗ₂ Lvl.⊔ ℓₒ}
  _⊆_ S₁ S₂ = (∀{x} → (x ∈₁ S₁) → (x ∈₂ S₂)) where
    _∈₁_ = _∈_ {ℓₗ₁}
    _∈₂_ = _∈_ {ℓₗ₂}

  -- A statement of whether a set is a superset of a set
  _⊇_ : ∀{T} → PredSet{ℓₗ₁}{ℓₒ}(T) → PredSet{ℓₗ₂}{ℓₒ}(T) → Stmt{ℓₗ₁ Lvl.⊔ ℓₗ₂ Lvl.⊔ ℓₒ}
  _⊇_ S₁ S₂ = (∀{x} → (x ∈₁ S₁) ← (x ∈₂ S₂)) where
    _∈₁_ = _∈_ {ℓₗ₁}
    _∈₂_ = _∈_ {ℓₗ₂}

  -- A statement of whether a set is equivalent to a set
  _≡_ : ∀{T} → PredSet{ℓₗ₁}{ℓₒ}(T) → PredSet{ℓₗ₂}{ℓₒ}(T) → Stmt{ℓₗ₁ Lvl.⊔ ℓₗ₂ Lvl.⊔ ℓₒ}
  _≡_ S₁ S₂ = ((S₁ ⊇ S₂)∧(S₁ ⊆ S₂))

module _ {ℓₗ}{ℓₒ} where
  ℘_ : ∀{T} → PredSet{ℓₗ}{ℓₒ}(T) → PredSet{ℓₗ}{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)}(PredSet{ℓₗ}{ℓₒ}(T))
  ℘_ S x = Lvl.Up(x ⊆' S) where
    _⊆'_ = _⊆_ {ℓₗ}{ℓₗ}{ℓₒ}

  _⋃_ : ∀{T} → PredSet{ℓₗ}{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)}(PredSet{ℓₗ}{ℓₒ}(T)) → PredSet{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)}{ℓₒ}(T)
  _⋃_ S x = Logic.Predicate.∃{Lvl.𝐒(ℓₗ)}{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)}(s ↦ (s ∈₁ S) ⨯ (x ∈₂ s)) where
    open import Data.Tuple as Tuple using (_⨯_ ; _,_)

    _∈₁_ = _∈_ {Lvl.𝐒(ℓₗ)}{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)}
    _∈₂_ = _∈_ {ℓₗ}{ℓₒ}

  _⋂_ : ∀{T} → PredSet{ℓₗ}{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)}(PredSet{ℓₗ}{ℓₒ}(T)) → PredSet{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)}{ℓₒ}(T)
  _⋂_ {T} S x = (∀{s : PredSet{ℓₗ}{ℓₒ}(T)} → (s ∈₁ S) → (x ∈₂ s)) where
    _∈₁_ = _∈_ {Lvl.𝐒(ℓₗ)}{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)}
    _∈₂_ = _∈_ {ℓₗ}{ℓₒ}

-- TODO: Idea (Does it work?): (Pseudo-code) Sets with anything using existential: AnySet = PredSet(∃{Type}(T ↦ t ∈ T))
