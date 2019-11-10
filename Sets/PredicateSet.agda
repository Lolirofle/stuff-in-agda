-- Sets represented by unary predicates (Like restricted comprehension)
-- Similiar to BoolSet, but instead using the builtin constructive logic with levels.
module Sets.PredicateSet where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Functional
open import Functional.Proofs
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
import      Relator.Equals as Equals
open import Relator.Equals.Proofs.Equivalence
open import Structure.Function.Domain
open import Type

module _ where
  -- A set
  -- Note: It is only within a certain type, so everything Pred{T} is actually a subset of T if T were a set.
  PredSet : ∀{ℓ ℓₒ} → Type{ℓₒ} → Type{Lvl.𝐒(ℓ) ⊔ ℓₒ}
  PredSet{ℓ}{ℓₒ} (T) = (T → Stmt{ℓ})

  private variable ℓ ℓ₁ ℓ₂ ℓₒ : Lvl.Level
  private variable T : Type{ℓₒ}

  -- The statement of whether an element is in a set
  -- TODO: Maybe define this using a equivalence relation instead? (Alternatively a Setoid: x ∈ S = ∃(y ↦ (x ≡_T y) ∧ S(y)))
  _∈_ : T → PredSet{ℓ}(T) → Stmt
  _∈_ = apply -- (x ∈ S) = S(x)

  _∉_ : T → PredSet{ℓ}(T) → Stmt
  _∉_ = (¬_) ∘₂ (_∈_) -- (x ∉ S) = ¬(x ∈ S)

  _∋_ : PredSet{ℓ}(T) → T → Stmt
  _∋_ = swap(_∈_) -- (S ∋ x) = (x ∈ S)

  _∌_ : PredSet{ℓ}(T) → T → Stmt
  _∌_ = (¬_) ∘₂ (_∋_) -- (S ∌ x) = ¬(S ∋ x)

  -- An empty set
  ∅ : PredSet{ℓ}(T)
  ∅ = const(Empty)

  -- An universal set
  -- Note: It is only within a certain type, so 𝐔{T} is actually a subset of everything. It is the subset containing only T if T were a set.
  𝐔 : PredSet{ℓ}(T)
  𝐔 = const(Unit)

  -- A singleton set (a set with only one element)
  •_ : T → PredSet(T)
  •_ = (Equals._≡_)

  -- An union of two sets
  _∪_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → PredSet(T)
  _∪_ S₁ S₂ x = (S₁(x) ∨ S₂(x))

  -- An union of a set and a singleton set
  _∪•_ : ∀{ℓ}{T : Type{ℓ}} → PredSet{ℓ₁}(T) → Type{ℓ} → PredSet(T)
  _∪•_ S P x = (S(x) ∨ P)

  -- An intersection of two sets
  _∩_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → PredSet(T)
  _∩_ S₁ S₂ x = (S₁(x) ∧ S₂(x))

  -- A complement of a set
  ∁_ : PredSet{ℓ}(T) → PredSet(T)
  ∁_ = (¬_) ∘_ -- ∁_ S x = (¬ S(x))

  _∖_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → PredSet(T)
  _∖_ S₁ S₂ = (S₁ ∩ (∁ S₂))

  filter : (T → Bool) → PredSet{ℓ}(T) → PredSet(T)
  filter f S x = (S(x) ∧ IsTrue(f(x)))

  -- A statement of whether a set is a subset of a set
  _⊆_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → Stmt
  _⊆_ S₁ S₂ = (∀{x} → (x ∈ S₁) → (x ∈ S₂))

  -- A statement of whether a set is a superset of a set
  _⊇_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → Stmt
  _⊇_ S₁ S₂ = (∀{x} → (x ∈ S₁) ← (x ∈ S₂))

  -- A statement of whether a set is equivalent to a set
  _≡_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → Stmt
  _≡_ S₁ S₂ = (∀{x} → (x ∈ S₁) ↔ (x ∈ S₂))

  Disjoint : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → Stmt
  Disjoint S₁ S₂ = ((S₁ ∩ S₂) ⊆ (∅ {Lvl.𝟎}))

  Overlapping : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → Stmt
  Overlapping S₁ S₂ = ∃(S₁ ∩ S₂)

  module _ where -- TODO: These proofs should be generalized somewhere else?
    private variable S₁ : PredSet{ℓ₁}(T)
    private variable S₂ : PredSet{ℓ₂}(T)

    [≡]-to-[⊆] : (S₁ ≡ S₂) → (S₁ ⊆ S₂)
    [≡]-to-[⊆] S₁S₂ {x} = [↔]-to-[→] (S₁S₂{x})

    [≡]-to-[⊇] : (S₁ ≡ S₂) → (S₁ ⊇ S₂)
    [≡]-to-[⊇] S₁S₂ {x} = [↔]-to-[←] (S₁S₂{x})

    [⊆]-of-[∪]ₗ : (S₁ ⊆ (S₁ ∪ S₂))
    [⊆]-of-[∪]ₗ = [∨]-introₗ

    [⊆]-of-[∪]ᵣ : (S₂ ⊆ (S₁ ∪ S₂))
    [⊆]-of-[∪]ᵣ = [∨]-introᵣ

    [∪]-of-subset : (S₁ ⊆ S₂) → ((S₁ ∪ S₂) ≡ S₂)
    [∪]-of-subset S₁S₂ = [↔]-intro [∨]-introᵣ ([∨]-elim S₁S₂ id)

{-
module _ where
  private variable ℓ₁ ℓ₂ : Lvl.Level
  private variable A : Type{ℓ₁}
  private variable B : Type{ℓ₂}

  map : (f : A → B) → ⦃ _ : Bijective(f) ⦄ → PredSet(A) → PredSet(B)
  map f S x = S(inv(f)(x))
-}

{-
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
-}

-- TODO: Idea (Does it work?): (Pseudo-code) Sets with anything using existential: AnySet = PredSet(∃{Type}(T ↦ t ∈ T))
