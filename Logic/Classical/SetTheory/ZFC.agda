open import Logic.Classical.NaturalDeduction

module Logic.Classical.SetTheory.ZFC {ℓₗ} {ℓₒ} ⦃ _ : PredicateEq{ℓₗ}{ℓₒ} ⦄ (_∈_ : Domain → Domain → Stmt) where

open import Functional
import      Lvl
open import Type

-- The statement that the set s is empty
Empty : Domain → Stmt
Empty(s) = ∀ₗ(x ↦ ¬(x ∈ s))

-- The statement that the set s is non-empty
NonEmpty : Domain → Stmt
NonEmpty(s) = ∃ₗ(x ↦ (x ∈ s))

-- The statement that the sets s₁ and s₂ are disjoint
Disjoint : Domain → Domain → Stmt
Disjoint(s₁)(s₂) = ¬ ∃ₗ(x ↦ (x ∈ s₁)∧(x ∈ s₂))

-- The statement that the set s is a function
-- Function : Domain → Stmt
-- Function(s) = ∀ₗ(x ↦ ∃ₗ!(y ↦ (x , y) ∈ s))

_∋_ : Domain → Domain → Stmt
_∋_ a x = (x ∈ a)

_∌_ : Domain → Domain → Stmt
_∌_ a x = ¬(x ∈ a)

_∉_ : Domain → Domain → Stmt
_∉_ x a = ¬(x ∈ a)

_⊆_ : Domain → Domain → Stmt
_⊆_ a b = ∀ₗ(x ↦ (x ∈ a) ⟶ (x ∈ b))

_⊇_ : Domain → Domain → Stmt
_⊇_ a b = ∀ₗ(x ↦ (x ∈ a) ⟵ (x ∈ b))

module Axioms where
  -- A set which is empty exists.
  -- • Allows a construction of the empty set.
  EmptySet = ∃ₗ(x ↦ Empty(x))

  -- A set with two elements exists.
  -- • Allows a construction of a set with two elements.
  Pairing = ∀ₗ(x₁ ↦ ∀ₗ(x₂ ↦ ∃ₗ(s ↦ ∀ₗ(x ↦ ((x ∈ s) ⟷ (x ≡ x₁)∨(x ≡ x₂))))))

  -- A set which is the subset of a set where all elements satisfies a predicate exists.
  RestrictedComprehension = ∀{φ : Domain → Stmt} → ∀ₗ(s ↦ ∃ₗ(sₛ ↦ ∀ₗ(x ↦ ((x ∈ sₛ) ⟷ ((x ∈ s) ∧ φ(x))))))

  -- A set which contains all the subsets of a set exists.
  -- • Allows a construction of a set that is the powerset of a set.
  PowerSet = ∀ₗ(s ↦ ∃ₗ(sₚ ↦ ∀ₗ(x ↦ (x ∈ sₚ) ⟷ (x ⊆ s))))

  -- A set which contains all the elements of a group of sets exists.
  -- • Allows a construction of a set that is the union of some sets.
  Union = ∀ₗ(ss ↦ ∃ₗ(sᵤ ↦ ∀ₗ(x ↦ ∀ₗ(s ↦ ((x ∈ sᵤ) ⟷ (x ∈ s)∧(s ∈ ss))))))

  -- Infinity

  -- Set equality is determined by its contents.
  -- • Guarantees the definition of equality for sets.
  Extensionality = ∀ₗ(s₁ ↦ ∀ₗ(s₂ ↦ ∀ₗ(x ↦ (x ∈ s₁)⟷(x ∈ s₂)) ⟷ (s₁ ≡ s₂)))

  -- A non-empty set contain sets that are disjoint to it.
  -- • Prevents sets containing themselves.
  -- • Making every set have a ordinal rank.
  Regularity = ∀ₗ(s₁ ↦ (NonEmpty(s₁) ⟶ ∃ₗ(s₂ ↦ (s₂ ∈ s₁) ∧ Disjoint(s₁)(s₂))))

  -- Replacement

record ZF : Type{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
record ZFC : Type{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
