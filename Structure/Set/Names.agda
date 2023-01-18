module Structure.Set.Names where

open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Tuple using (_⨯_ ; _,_)
open import Functional
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Function
open import Structure.Relator
open import Structure.Setoid using (Equiv) renaming (_≡_ to _≡ₛ_ ; _≢_ to _≢ₛ_)
open import Type
open import Type.Dependent.Sigma
open import Type.Properties.Inhabited

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ ℓ₉ ℓ₁₀ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑₑ ℓₑₑₒ ℓₑₑₗ ℓₑₑᵣ ℓₑᵢ ℓₑₒ ℓₑₛ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ ℓᵣ ℓₒ ℓᵣₑₗ ℓₛ : Lvl.Level
private variable A B C S S₁ S₂ Sₒ Sᵢ Sₗ Sᵣ E E₁ E₂ Eₒ Eₗ Eᵣ I O : Type{ℓ}
private variable _∈ₒ_ _∈ᵢ_ : E → S → Stmt{ℓₗ}
private variable _∈ₗ_ : E → Sₗ → Stmt{ℓₗ}
private variable _∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}

-- Derivable relation symbols from the subset relation.
module From-[⊆] (_⊆_ : Sₗ → Sᵣ → Stmt{ℓₗ}) where
  -- Superset.
  -- (A ⊇ B) means that every element in the set B is also in the set A (A contains the contents of B).
  _⊇_ = swap(_⊆_)

  -- Non-subset.
  _⊈_ = (¬_) ∘₂ (_⊆_)

  -- Non-superset.
  _⊉_ = (¬_) ∘₂ (_⊇_)

-- Derivable relation symbols from two membership relations.
module From-[∈][∈] (_∈ₗ_ : E → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}) where
  -- Subset.
  -- (A ⊆ B) means that every element in the set A is also in the set B (A is a part of B).
  -- Alternative definition:
  --   A ↦ B ↦ ∀ₗ(x ↦ ((_→ᶠ_) on₂ (x ∈_)) A B)
  _⊆_ = \A B → ∀{x} → (x ∈ₗ A) → (x ∈ᵣ B)

  -- Set equality.
  -- (A ≡ B) means that the sets A and B contains the same elements.
  _≡_ = \A B → ∀{x} → (x ∈ₗ A) ↔ (x ∈ᵣ B)

  open From-[⊆] (_⊆_) public

-- Derivable relation symbols from the membership relation.
module From-[∈] (_∈_ : E → S → Stmt{ℓₗ}) where
  -- Containment.
  -- (a ∋ x) means that the set a contains the element x.
  _∋_ = swap(_∈_)

  -- Not element of.
  _∉_ = (¬_) ∘₂ (_∈_)

  -- Non-containment.
  _∌_ = (¬_) ∘₂ (_∋_)

  open From-[∈][∈] (_∈_)(_∈_) public

module From-[∋] (_∋_ : S → E → Stmt{ℓₗ}) where
  _∈_ = swap(_∋_)

  open From-[∈] (_∈_) hiding (_∋_) public

module Relations (_∈_ : E → S → Stmt{ℓₗ}) where
  -- The property of a set being empty.
  Empty : S → Type
  Empty(s) = ∀ₗ(x ↦ ¬(x ∈ s))

  -- The property of a set being non-empty.
  NonEmpty : S → Type
  NonEmpty(s) = ∃(_∈ s)

  -- The property of a set being the universal set (containing all elements).
  Universal : S → Type
  Universal(s) = ∀ₗ(_∈ s)

  -- The property of two sets being disjoint (not sharing any elements).
  Disjoint : S → S → Type
  Disjoint s₁ s₂ = ∀ₗ(x ↦ ((x ∈ s₁) → (x ∈ s₂) → ⊥))

module One (_∈_ : E → S → Stmt{ℓₗ}) where
  open From-[∈] (_∈_)

  -- The empty set containing no elements.
  -- No elements are in the empty set.
  -- Standard set notation: ∅ = {}.
  EmptyMembership     = \(∅)
                      → ∀{x} → (x ∉ ∅)

  -- The universal set containing all elements.
  -- Every element is in the universal set.
  -- Standard set notation: 𝐔 = {x. ⊤}.
  UniversalMembership = \(𝐔)
                      → ∀{x} → (x ∈ 𝐔)

  module _ {I : Type{ℓ}} ⦃ equiv-I : Equiv{ℓₑᵢ}(I) ⦄ ⦃ equiv-E : Equiv{ℓₑₑ}(E) ⦄ where
  -- The image of a function containing the elements that the function points to.
  -- The elements of the form f(x) for any x.
  -- Standard set notation: ⊶ f = {f(x). (x: I)}.
    ImageMembership = \(⊶ : (f : I → E) → ⦃ func : Function(f) ⦄ → S)
                    → ∀{f} ⦃ func : Function(f) ⦄ → ∀{y} → (y ∈ (⊶ f)) ↔ ∃(x ↦ f(x) ≡ₛ y)

  module _ ⦃ equiv-E : Equiv{ℓₑₑ}(E) ⦄ {O : Type{ℓ}} ⦃ equiv-O : Equiv{ℓₑₒ}(O) ⦄ where
    -- The fiber of a function together with one of its values containing the elements that point to this value.
    -- Standard set notation: fiber f(y) = {x. f(x) ≡ y}
    FiberMembership = \(fiber : (f : E → O) → ⦃ func : Function(f) ⦄ → (O → S))
                    → ∀{f} ⦃ func : Function(f) ⦄ {y}{x} → (x ∈ fiber f(y)) ↔ (f(x) ≡ₛ y)

  module _ ⦃ equiv-E : Equiv{ℓₑₑ}(E) ⦄ where
    -- The singleton set of a single element containing only this element.
    -- Standard set notation: singleton(x) = {x}
    SingletonMembership = \(singleton : E → S)
                        → ∀{y}{x} → (x ∈ singleton(y)) ↔ (x ≡ₛ y)

    -- The pair set of two elements containing only the two elements.
    -- Standard set notation: pair x y = {x,y}
    PairMembership      = \(pair : E → E → S)
                        → ∀{y₁ y₂}{x} → (x ∈ pair y₁ y₂) ↔ ((x ≡ₛ y₁) ∨ (x ≡ₛ y₂))

    module _ {ℓ} where
      -- Set comprehension with a predicate containing all elements that satisfy this predicate.
      -- Also called: Unrestricted set comprehension, set-builder notation.
      -- Standard set notation: comp(P) = {x. P(x)}
      ComprehensionMembership = \(comp : (P : E → Stmt{ℓ}) ⦃ unaryRelator : UnaryRelator(P) ⦄ → S)
                              → ∀{P} ⦃ unaryRelator : UnaryRelator(P) ⦄ {x} → (x ∈ comp(P)) ↔ P(x)
open One public

module Two (_∈ₗ_ : E → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}) where
  private module Def = From-[∈][∈] (_∈ₗ_)(_∈ᵣ_)

  SubsetMembership      = \{ℓᵣₑₗ} (_⊆_ : Sₗ → Sᵣ → Stmt{ℓᵣₑₗ})
                        → ∀{a b} → (a ⊆ b) ↔ (a Def.⊆ b)
  SetEqualityMembership = \{ℓᵣₑₗ} (_≡_ : Sₗ → Sᵣ → Stmt{ℓᵣₑₗ})
                        → ∀{a b} → (a ≡ b) ↔ (a Def.≡ b)
open Two public

module TwoSame (_∈ₗ_ : E → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}) where
  -- The set complement of a set containing all elements not in this set.
  -- Standard set notation: ∁ A =  {x. x ∉ A}
  ComplementMembership  = \(∁ : Sₗ → Sᵣ)
                        → ∀{A}{x} → (x ∈ᵣ (∁ A)) ↔ ¬(x ∈ₗ A)

  module _ ⦃ equiv-E : Equiv{ℓₑₑ}(E) ⦄ where
    AddMembership       = \(add : E → Sₗ → Sᵣ)
                        → ∀{y}{a}{x} → (x ∈ᵣ add y a) ↔ ((x ∈ₗ a) ∨ (x ≡ₛ y))
    RemoveMembership    = \(remove : E → Sₗ → Sᵣ)
                        → ∀{y}{a}{x} → (x ∈ᵣ remove y a) ↔ ((x ∈ₗ a) ∧ (x ≢ₛ y))

    module _ {ℓ} where
      -- The filtering of a set with a predicate containing all elements in the set that satisfy the predicate.
      -- It is the subset where all elements satisfy the predicate.
      -- Standard set notation: filter P(A) =  {(x∊A). P(x)}
      FilterMembership = \(filter : (P : E → Stmt{ℓ}) ⦃ unaryRelator : UnaryRelator(P) ⦄ → (Sₗ → Sᵣ))
                       → ∀{A}{P} ⦃ unaryRelator : UnaryRelator(P) ⦄ {x} → (x ∈ᵣ filter P(A)) ↔ ((x ∈ₗ A) ∧ P(x))

  -- The filtering of a set with a boolean predicate containing all elements in the set that satisfy the predicate.
  -- Standard set notation: boolFilter P(A) =  {(x∊A). P(x) ≡ 𝑇}
  BooleanFilterMembership = \(boolFilter : (E → Bool) → (Sₗ → Sᵣ))
                          → ∀{A}{P}{x} → (x ∈ᵣ boolFilter P(A)) ↔ ((x ∈ₗ A) ∧ IsTrue(P(x)))

  -- The big union containing the elements that are in any of the sets in the image of a function.
  -- Standard set notation: ⋃ᵢ f = {x. ∃i. x ∈ f(i)}
  IndexedBigUnionMembership        = \{ℓ}{I : Type{ℓ}} (⋃ᵢ : (I → Sₗ) → Sᵣ)
                                   → ∀{Ai}{x} → (x ∈ᵣ (⋃ᵢ Ai)) ↔ ∃(i ↦ (x ∈ₗ Ai(i)))

  -- The big intersection containing the elements that are in all of the sets in the image of a function.
  -- Standard set notation: ⋃ᵢ f = {x. ∃i. x ∈ f(i)}
  IndexedBigIntersectionMembership = \{ℓ}{I : Type{ℓ}} (⋂ᵢ : (I → Sₗ) → Sᵣ)
                                   → ∀{Ai} → (◊ I) → ∀{x} → (x ∈ᵣ (⋂ᵢ Ai)) ↔ (∀{i} → (x ∈ₗ Ai(i)))
open TwoSame public

module TwoDifferent (_∈ₗ_ : Eₗ → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : Eᵣ → Sᵣ → Stmt{ℓᵣ}) where
  module _ ⦃ equiv-Eₗ : Equiv{ℓₑₑₗ}(Eₗ) ⦄ ⦃ equiv-Eᵣ : Equiv{ℓₑₑᵣ}(Eᵣ) ⦄ where
    -- The image of a function on a set containing the elements that the function points to from the set (the image of a function where the domain is restricted to the set).
    -- The elements of the form f(x) for any x in A.
    -- Standard set notation: map f(A) = {f(x). x ∈ A}.
    MapMembership = \(map : (f : Eₗ → Eᵣ) ⦃ func : Function(f) ⦄ → (Sₗ → Sᵣ))
                  → ∀{f} ⦃ func : Function(f) ⦄ {A}{y} → (y ∈ᵣ map f(A)) ↔ ∃(x ↦ (x ∈ₗ A) ∧ (f(x) ≡ₛ y))

    -- The inverse image of a function together with a set containing the elements that point to elements in the set.
    -- The elements x for any f(x) in A.
    -- Standard set notation: unmap f(A) = {x. f(x) ∈ A}
    UnmapMembership = \(unmap : (f : Eₗ → Eᵣ) ⦃ func : Function(f) ⦄ → (Sᵣ → Sₗ))
                    → ∀{f} ⦃ func : Function(f) ⦄ {A}{x} → (x ∈ₗ unmap f(A)) ↔ (f(x) ∈ᵣ A)
open TwoDifferent public

module Three (_∈ₗ_ : E → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}) (_∈ₒ_ : E → Sₒ → Stmt{ℓₒ}) where
  LogicalOperatorMembership = \{ℓ} (_△_ : Stmt{ℓₗ} → Stmt{ℓᵣ} → Stmt{ℓ}) (_▫_ : Sₗ → Sᵣ → Sₒ)
                            → (∀{A B}{x} → (x ∈ₒ (A ▫ B)) ↔ ((x ∈ₗ A) △ (x ∈ᵣ B)))

  -- The union of two sets containing the elements that are in at least one of the sets.
  -- Standard set notation: A ∪ B = {x. (x ∈ A) ∨ (x ∈ B)}
  -- Expanded implementation:
  --   UnionMembership = \(_∪_ : Sₗ → Sᵣ → Sₒ)
  --                   → (∀{A B}{x} → (x ∈ₒ (A ∪ B)) ↔ ((x ∈ₗ A) ∨ (x ∈ᵣ B)))
  UnionMembership = LogicalOperatorMembership(_∨_)

  -- The intersection of two sets containing the elements that are in at both of the sets.
  -- Standard set notation: A ∪ B = {x. (x ∈ A) ∨ (x ∈ B)}
  -- Expanded implementation:
  --   IntersectMembership = \(_∩_ : Sₗ → Sᵣ → Sₒ)
  --                       → (∀{A B}{x} → (x ∈ₒ (A ∩ B)) ↔ ((x ∈ₗ A) ∧ (x ∈ᵣ B)))
  IntersectMembership = LogicalOperatorMembership(_∧_)

  -- The relative complement of two sets containing the elements that are in the left set but not in the right.
  -- Standard set notation: A ∖ B = {x. (x ∈ A) ∧ (x ∉ B)}
  -- Expanded implementation:
  --   WithoutMembership = \(_∖_ : Sₗ → Sᵣ → Sₒ)
  --                     → (∀{A B}{x} → (x ∈ₒ (A ∖ B)) ↔ ((x ∈ₗ A) ∧ ¬(x ∈ᵣ B)))
  WithoutMembership = LogicalOperatorMembership(\A B → A ∧ ¬ B)

  -- The mapped big union containing the elements that are in any of the sets given by mapping a function on every element of a set.
  -- Standard set notation: ⋃$ A f = {x. ∃(a∊A). x ∈ f(a)}
  BigUnionMapMembership = \(⋃$ : (s : Sₗ) → ((x : E) → (x ∈ₗ s) → Sᵣ) → Sₒ)
                        → ∀{A}{f}{x} → (x ∈ₒ (⋃$ A f)) ↔ ∃(a ↦ Σ(a ∈ₗ A) (\p → (x ∈ᵣ f a p)))

  -- The mapped big intersection containing the elements that are in all of the sets given by mapping a function on every element of a set.
  -- Standard set notation: ⋃$ A f = {x. ∀(a∊A). x ∈ f(a)}
  BigIntersectMapMembership = \(⋂$ : (s : Sₗ) → ((x : E) → (x ∈ₗ s) → Sᵣ) → Sₒ)
                            → ∀{A}{f}{x} → (x ∈ₒ (⋂$ A f)) ↔ (∀{a}{p : a ∈ₗ A} → (x ∈ᵣ f a p))
open Three public

module ThreeDifferent (_∈ₗ_ : Eₗ → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : Eᵣ → Sᵣ → Stmt{ℓᵣ}) (_∈ₒ_ : Eₒ → Sₒ → Stmt{ℓₒ}) where
  module _ ⦃ equiv-Eₒ : Equiv{ℓₑₑₒ}(Eₒ) ⦄ where
    BinaryMapMembership = \(_△_ : Eₗ → Eᵣ → Eₒ) (_▫_ : Sₗ → Sᵣ → Sₒ)
                             → (∀{A B}{x} → (x ∈ₒ (A ▫ B)) ↔ ∃{Obj = Eₗ ⨯ Eᵣ}(\(a , b) → ((a ∈ₗ A) ∧ (b ∈ᵣ B)) ∧ (a △ b ≡ₛ x)))
open ThreeDifferent public

module ThreeNestedTwoDifferent (_∈ₒ_ : Sₗ → Sₒ → Stmt{ℓₒ}) where
  module _ (_⊆_ : Sₗ → Sᵣ → Stmt{ℓₛ}) where
    -- The power set of a set containing all subsets of a set.
    -- Standard set notation: ℘(y) = {x. x ⊆ y}
    PowerMembership = \(℘ : Sᵣ → Sₒ)
                    → ∀{y}{x} → (x ∈ₒ ℘(y)) ↔ (x ⊆ y)
open ThreeNestedTwoDifferent public

module ThreeTwoNested (_∈ₗ_ : E → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : Sₗ → Sᵣ → Stmt{ℓᵣ}) (_∈ₒ_ : E → Sₒ → Stmt{ℓₒ}) where
  -- The big union containing the elements that are in any of the sets in a set.
  -- Standard set notation: ⋃ A = {x. ∃(a∊A). x ∈ a}
  BigUnionMembership      = \(⋃ : Sᵣ → Sₒ)
                          → ∀{A}{x} → (x ∈ₒ (⋃ A)) ↔ ∃(a ↦ (a ∈ᵣ A) ∧ (x ∈ₗ a))

  -- The big intersection containing the elements that are in all of the sets in a non-empty set.
  -- Standard set notation: (A ≠ ∅) → (⋂ A = {x. ∀(a∊A). x ∈ a})
  BigIntersectionMembership = \(⋂ : Sᵣ → Sₒ)
                            → ∀{A} → ∃(_∈ᵣ A) → ∀{x} → (x ∈ₒ (⋂ A)) ↔ (∀{a} → (a ∈ᵣ A) → (x ∈ₗ a))

  -- The big intersection containing the elements that are in all of the sets in a set, unless the set is the empty set, in which the result is the empty set itself.
  -- Standard set notation:
  --   ⋂ A = {x. (∃(a∊A). x ∈ a) ∧ (∀(a∊A). x ∈ a)}
  --   ⋂ ∅ = ∅
  BigIntersectionMembershipWithEmpty = \(⋂ : Sᵣ → Sₒ)
                                     → ∀{A}{x} → (x ∈ₒ (⋂ A)) ↔ ∃(a ↦ (a ∈ᵣ A) ∧ (x ∈ₗ a)) ∧ (∀{a} → (a ∈ᵣ A) → (x ∈ₗ a))

  -- The big intersection containing the elements that are in all of the sets in a set.
  -- Note: Using this definition of the big intersection on the empty set results in the universal set.
  -- Standard set notation:
  --   ⋂ A = {x. (∀(a∊A). x ∈ a)}
  --   ⋂ ∅ = 𝐔
  BigIntersectionMembershipWithUniversal = \(⋂ : Sᵣ → Sₒ)
                                         → ∀{A}{x} → (x ∈ₒ (⋂ A)) ↔ (∀{a} → (a ∈ᵣ A) → (x ∈ₗ a))
open ThreeTwoNested public
