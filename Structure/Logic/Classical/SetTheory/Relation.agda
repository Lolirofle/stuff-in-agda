import Structure.Logic.Classical.NaturalDeduction

module Structure.Logic.Classical.SetTheory.Relation {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic : _ ⦄ (_∈_ : Domain → Domain → Formula) where
open Structure.Logic.Classical.NaturalDeduction.ClassicalLogic {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} (classicLogic)

open import Syntax.Function
open import Structure.Logic.Classical.SetTheory.BoundedQuantification {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic ⦄ (_∈_)

UnaryRelator : Set(_)
UnaryRelator = (Domain → Formula)

BinaryRelator : Set(_)
BinaryRelator = (Domain → Domain → Formula)

-- Containment
-- (a ∋ x) means that the set a contains the set x.
_∋_ : BinaryRelator
_∋_ a x = (x ∈ a)

-- Non-containment
_∌_ : BinaryRelator
_∌_ a x = ¬(x ∈ a)

-- Element of
_∉_ : BinaryRelator
_∉_ x a = ¬(x ∈ a)

-- Subset of
_⊆_ : BinaryRelator
_⊆_ a b = ∀ₗ(x ↦ (x ∈ a) ⟶ (x ∈ b))

-- Superset of
_⊇_ : BinaryRelator
_⊇_ a b = ∀ₗ(x ↦ (x ∈ a) ⟵ (x ∈ b))

-- The statement that the set s is empty
Empty : UnaryRelator
Empty(s) = ∀ₗ(x ↦ ¬(x ∈ s))

-- The statement that the set s is non-empty
NonEmpty : UnaryRelator
NonEmpty(s) = ∃ₗ(x ↦ (x ∈ s))

-- The statement that the sets s₁ and s₂ are disjoint
Disjoint : BinaryRelator
Disjoint(s₁)(s₂) = ∀ₗ(x ↦ ¬((x ∈ s₁)∧(x ∈ s₂)))
-- ¬ ∃ₗ(x ↦ (x ∈ s₁)∧(x ∈ s₂))

-- The statement that the sets in ss are all pairwise disjoint
PairwiseDisjoint : UnaryRelator
PairwiseDisjoint(ss) = ∀ₛ(ss)(s₁ ↦ ∀ₛ(ss)(s₂ ↦ ∀ₗ(x ↦ (x ∈ s₁)∧(x ∈ s₂) ⟶ (s₁ ≡ s₂))))
-- ∀ₛ(ss)(s₁ ↦ ∀ₛ(ss)(s₂ ↦ (s₁ ≢ s₂) → Disjoint(s₁)(s₂)))

-- The statement that the relation predicate F is a partial function
PartialFunction : BinaryRelator → Domain → Formula
PartialFunction(F) (dom) = ∀ₛ(dom)(x ↦ Unique(y ↦ F(x)(y)))

-- The statement that the relation predicate F is a total function
TotalFunction : BinaryRelator → Domain → Formula
TotalFunction(F) (dom) = ∀ₛ(dom)(x ↦ ∃ₗ!(y ↦ F(x)(y)))
