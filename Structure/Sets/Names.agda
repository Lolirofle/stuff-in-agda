module Structure.Sets.Names where

open import Data.Boolean
open import Data.Boolean.Stmt
open import Functional
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Function
open import Structure.Relator
open import Structure.Setoid using (Equiv) renaming (_≡_ to _≡ₛ_ ; _≢_ to _≢ₛ_)
open import Type
open import Type.Properties.Inhabited

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ ℓ₉ ℓ₁₀ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ ℓᵣ ℓₒ ℓᵣₑₗ ℓₛ : Lvl.Level
private variable A B C S S₁ S₂ Sₒ Sᵢ Sₗ Sᵣ E E₁ E₂ Eₗ Eᵣ I O : Type{ℓ}
private variable _∈_ _∈ₒ_ _∈ᵢ_ : E → S → Stmt{ℓₗ}
private variable _∈ₗ_ : E → Sₗ → Stmt{ℓₗ}
private variable _∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}

module From-[∈] (_∈_ : E → S → Stmt{ℓₗ}) where
  _∋_ = swap(_∈_)
  _∉_ = (¬_) ∘₂ (_∈_)
  _∌_ = (¬_) ∘₂ (_∋_)

module From-[⊆] (_⊆_ : Sₗ → Sᵣ → Stmt{ℓₗ}) where
  _⊇_ = swap(_⊆_)
  _⊈_ = (¬_) ∘₂ (_⊆_)
  _⊉_ = (¬_) ∘₂ (_⊇_)

module One (_∈_ : E → S → Stmt{ℓₗ}) where
  open From-[∈] (_∈_)

  EmptyMembership     = \(∅)
                      → ∀{x} → (x ∉ ∅)
  UniversalMembership = \(𝐔)
                      → ∀{x} → (x ∈ 𝐔)

  module _ {I : Type{ℓ}} ⦃ equiv-I : Equiv{ℓₗ₁}(I) ⦄ ⦃ equiv-E : Equiv{ℓₗ₂}(E) ⦄ where
    ImageMembership = \(⊶ : (f : I → E) → ⦃ func : Function(f) ⦄ → S)
                    → ∀{f} ⦃ func : Function(f) ⦄ → ∀{y} → (y ∈ (⊶ f)) ↔ ∃(x ↦ f(x) ≡ₛ y)

  module _ ⦃ equiv-E : Equiv{ℓₗ₂}(E) ⦄ {O : Type{ℓ}} ⦃ equiv-O : Equiv{ℓₗ₁}(O) ⦄ where
    FiberMembership = \(fiber : (f : E → O) → ⦃ func : Function(f) ⦄ → (O → S))
                    → ∀{f} ⦃ func : Function(f) ⦄ {y}{x} → (x ∈ fiber f(y)) ↔ (f(x) ≡ₛ y)

  module _ ⦃ equiv-E : Equiv{ℓₗ}(E) ⦄ where
    SingletonMembership = \(singleton : E → S)
                        → ∀{y}{x} → (x ∈ singleton(y)) ↔ (x ≡ₛ y)
    PairMembership      = \(pair : E → E → S)
                        → ∀{y₁ y₂}{x} → (x ∈ pair y₁ y₂) ↔ ((x ≡ₛ y₁) ∨ (x ≡ₛ y₂))

    module _ {ℓ} where
      ComprehensionMembership = \(comp : (P : E → Stmt{ℓ}) ⦃ unaryRelator : UnaryRelator(P) ⦄ → S)
                              → ∀{P} ⦃ unaryRelator : UnaryRelator(P) ⦄ {x} → (x ∈ comp(P)) ↔ P(x)
open One public

module Two (_∈ₗ_ : E → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}) where
  _⊆_ = \A B → ∀{x} → (x ∈ₗ A) → (x ∈ᵣ B)
  _⊇_ = \A B → ∀{x} → (x ∈ₗ A) ← (x ∈ᵣ B)
  _≡_ = \A B → ∀{x} → (x ∈ₗ A) ↔ (x ∈ᵣ B)

  SubsetMembership      = \{ℓᵣₑₗ} (_⊆_ : Sₗ → Sᵣ → Stmt{ℓᵣₑₗ})
                        → ∀{a b} → (a ⊆ b) ↔ (∀{x} → (x ∈ₗ a) → (x ∈ᵣ b))
  SetEqualityMembership = \{ℓᵣₑₗ} (_≡_ : Sₗ → Sᵣ → Stmt{ℓᵣₑₗ})
                        → ∀{a b} → (a ≡ b) ↔ (∀{x} → (x ∈ₗ a) ↔ (x ∈ᵣ b))

  ComplementMembership  = \(∁ : Sₗ → Sᵣ)
                        → ∀{A}{x} → (x ∈ᵣ (∁ A)) ↔ ¬(x ∈ₗ A)

  module _ ⦃ equiv-E : Equiv{ℓₗ}(E) ⦄ where
    AddMembership       = \(add : E → Sₗ → Sᵣ)
                        → ∀{y}{a}{x} → (x ∈ᵣ add y a) ↔ ((x ∈ₗ a) ∨ (x ≡ₛ y))
    RemoveMembership    = \(remove : E → Sₗ → Sᵣ)
                        → ∀{y}{a}{x} → (x ∈ᵣ remove y a) ↔ ((x ∈ₗ a) ∧ (x ≢ₛ y))

    module _ {ℓ} where
      FilterMembership = \(filter : (P : E → Stmt{ℓ}) ⦃ unaryRelator : UnaryRelator(P) ⦄ → (Sₗ → Sᵣ))
                       → ∀{A}{P} ⦃ unaryRelator : UnaryRelator(P) ⦄ {x} → (x ∈ᵣ filter P(A)) ↔ ((x ∈ₗ A) ∧ P(x))

  BooleanFilterMembership = \(boolFilter : (E → Bool) → (Sₗ → Sᵣ))
                          → ∀{A}{P}{x} → (x ∈ᵣ boolFilter P(A)) ↔ ((x ∈ₗ A) ∧ IsTrue(P(x)))

  IndexedBigUnionMembership        = \{ℓ}{I : Type{ℓ}} (⋃ᵢ : (I → Sₗ) → Sᵣ)
                                   → ∀{Ai}{x} → (x ∈ᵣ (⋃ᵢ Ai)) ↔ ∃(i ↦ (x ∈ₗ Ai(i)))
  IndexedBigIntersectionMembership = \{ℓ}{I : Type{ℓ}} (⋂ᵢ : (I → Sₗ) → Sᵣ)
                                   → ∀{Ai} → (◊ I) → ∀{x} → (x ∈ᵣ (⋂ᵢ Ai)) ↔ (∀{i} → (x ∈ₗ Ai(i)))
open Two public

module TwoDifferent (_∈ₗ_ : Eₗ → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : Eᵣ → Sᵣ → Stmt{ℓᵣ}) where
  module _ ⦃ equiv-Eₗ : Equiv{ℓₗ₁}(Eₗ) ⦄ ⦃ equiv-Eᵣ : Equiv{ℓₗ₂}(Eᵣ) ⦄ where
    MapMembership = \(map : (f : Eₗ → Eᵣ) ⦃ func : Function(f) ⦄ → (Sₗ → Sᵣ))
                  → ∀{f} ⦃ func : Function(f) ⦄ {A}{y} → (y ∈ᵣ map f(A)) ↔ ∃(x ↦ (x ∈ₗ A) ∧ (f(x) ≡ₛ y))
    UnmapMembership = \(unmap : (f : Eₗ → Eᵣ) ⦃ func : Function(f) ⦄ → (Sᵣ → Sₗ))
                    → ∀{f} ⦃ func : Function(f) ⦄ {A}{x} → (x ∈ₗ unmap f(A)) ↔ (f(x) ∈ᵣ A)
open TwoDifferent public

module Three (_∈ₗ_ : E → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}) (_∈ₒ_ : E → Sₒ → Stmt{ℓₒ}) where
  UnionMembership     = \(_∪_ : Sₗ → Sᵣ → Sₒ)
                      → (∀{A B}{x} → (x ∈ₒ (A ∪ B)) ↔ ((x ∈ₗ A) ∨ (x ∈ᵣ B)))
  IntersectMembership = \(_∩_ : Sₗ → Sᵣ → Sₒ)
                      → (∀{A B}{x} → (x ∈ₒ (A ∩ B)) ↔ ((x ∈ₗ A) ∧ (x ∈ᵣ B)))
  WithoutMembership   = \(_∖_ : Sₗ → Sᵣ → Sₒ)
                      → (∀{A B}{x} → (x ∈ₒ (A ∖ B)) ↔ ((x ∈ₗ A) ∧ ¬(x ∈ᵣ B)))
open Three public

module ThreeNestedTwoDifferent (_∈ₒ_ : Sₗ → Sₒ → Stmt{ℓₒ}) where
  module _ (_⊆_ : Sₗ → Sᵣ → Stmt{ℓₛ}) where
    PowerMembership = \(℘ : Sᵣ → Sₒ)
                    → ∀{y}{x} → (x ∈ₒ ℘(y)) ↔ (x ⊆ y)
open ThreeNestedTwoDifferent public

module ThreeTwoNested (_∈ₗ_ : E → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : Sₗ → Sᵣ → Stmt{ℓᵣ}) (_∈ₒ_ : E → Sₒ → Stmt{ℓₒ}) where
  BigUnionMembership      = \(⋃ : Sᵣ → Sₒ)
                          → ∀{A}{x} → (x ∈ₒ (⋃ A)) ↔ ∃(a ↦ (a ∈ᵣ A) ∧ (x ∈ₗ a))
  BigIntersectionMembership = \(⋂ : Sᵣ → Sₒ)
                          → ∀{A} → ∃(_∈ᵣ A) → ∀{x} → (x ∈ₒ (⋂ A)) ↔ (∀{a} → (a ∈ᵣ A) → (x ∈ₗ a))
open ThreeTwoNested public
