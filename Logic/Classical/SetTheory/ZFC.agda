open import Metalogic.Classical.NaturalDeduction

module Logic.Classical.SetTheory.ZFC {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} {Proof} {Construct} ⦃ _ : PredicateEq.Theory{ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} (Proof) (Construct) ⦄ (_∈_ : Domain → Domain → Stmt) where

open import Functional hiding (Domain)
import      Lvl
open import Type
open        Metalogic.Classical.NaturalDeduction.PredicateEq {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} (Proof) (Construct) using () renaming (Theory to PredicateEqTheory)
open        PredicateEqTheory ⦃ ... ⦄

-- The statement that the set s is empty
Empty : Domain → Stmt
Empty(s) = ∀ₗ(x ↦ ¬(x ∈ s))

-- The statement that the set s is non-empty
NonEmpty : Domain → Stmt
NonEmpty(s) = ∃ₗ(x ↦ (x ∈ s))

-- The statement that the sets s₁ and s₂ are disjoint
Disjoint : Domain → Domain → Stmt
Disjoint(s₁)(s₂) = ¬ ∃ₗ(x ↦ (x ∈ s₁)∧(x ∈ s₂))

-- The statement that the predicate F is a partial function
PartialFunction : (Domain → Domain → Stmt) → Domain → Stmt
PartialFunction(F) (dom) = ∀ₗ(x ↦ (x ∈ dom) ⟶ Unique(y ↦ F(x)(y)))

-- The statement that the predicate F is a total function
TotalFunction : (Domain → Domain → Stmt) → Domain → Stmt
TotalFunction(F) (dom) = ∀ₗ(x ↦ (x ∈ dom) ⟶ ∃ₗ!(y ↦ F(x)(y)))

-- The statement that the set s is a function
-- FunctionSet : Domain → Stmt
-- FunctionSet(s) = ∀ₗ(x ↦ ∃ₗ!(y ↦ (x , y) ∈ s))

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

-- 𝟎 : Domain

module Axioms where
  -- A set which is empty exists.
  -- • Allows a construction of the empty set.
  EmptySet = Proof(∃ₗ(x ↦ Empty(x)))

  -- A set with two elements exists.
  -- • Allows a construction of a set with two elements.
  Pairing = Proof(∀ₗ(x₁ ↦ ∀ₗ(x₂ ↦ ∃ₗ(s ↦ ∀ₗ(x ↦ ((x ∈ s) ⟷ (x ≡ x₁)∨(x ≡ x₂)))))))

  -- A set which is the subset of a set where all elements satisfies a predicate exists.
  RestrictedComprehension = ∀{φ : Domain → Stmt} → Proof(∀ₗ(s ↦ ∃ₗ(sₛ ↦ ∀ₗ(x ↦ ((x ∈ sₛ) ⟷ ((x ∈ s) ∧ φ(x)))))))

  -- A set which contains all the subsets of a set exists.
  -- • Allows a construction of a set that is the powerset of a set.
  PowerSet = Proof(∀ₗ(s ↦ ∃ₗ(sₚ ↦ ∀ₗ(x ↦ (x ∈ sₚ) ⟷ (x ⊆ s)))))

  -- A set which contains all the elements of a group of sets exists.
  -- • Allows a construction of a set that is the union of some sets.
  Union = Proof(∀ₗ(ss ↦ ∃ₗ(sᵤ ↦ ∀ₗ(x ↦ ∀ₗ(s ↦ ((x ∈ sᵤ) ⟷ (x ∈ s)∧(s ∈ ss)))))))

  Infinity = Proof(⊤) -- TODO

  -- Set equality is determined by its contents.
  -- • Guarantees the definition of equality for sets.
  Extensionality = Proof(∀ₗ(s₁ ↦ ∀ₗ(s₂ ↦ ∀ₗ(x ↦ (x ∈ s₁)⟷(x ∈ s₂)) ⟷ (s₁ ≡ s₂))))

  -- A non-empty set contain sets that are disjoint to it.
  -- • Prevents sets containing themselves.
  -- • Making every set have a ordinal rank.
  Regularity = Proof(∀ₗ(s₁ ↦ (NonEmpty(s₁) ⟶ ∃ₗ(s₂ ↦ (s₂ ∈ s₁) ∧ Disjoint(s₁)(s₂)))))

  Replacement = ∀{φ : Domain → Domain → Stmt} → Proof(∀ₗ(A ↦ TotalFunction(φ)(A) ⟶ ∃ₗ(B ↦ ∀ₗ(y ↦ (y ∈ B) ⟷ ∃ₗ(x ↦ (x ∈ A) ∧ φ(x)(y))))))

  Choice = Proof(⊤)

record ZF : Type{(ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ (ℓₘₗ Lvl.⊔ ℓₘₒ)} where
  open Axioms

  field
    extensional   : Extensionality
    regular       : Regularity
    comprehension : RestrictedComprehension
    pairing       : Pairing
    union         : Union
    replacement   : Replacement
    infinity      : Infinity
    power         : PowerSet

record ZFC : Type{(ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ (ℓₘₗ Lvl.⊔ ℓₘₒ)} where
  open Axioms

  field
    extensional   : Extensionality
    regular       : Regularity
    comprehension : RestrictedComprehension
    pairing       : Pairing
    union         : Union
    replacement   : Replacement
    infinity      : Infinity
    power         : PowerSet
    choice        : Choice
