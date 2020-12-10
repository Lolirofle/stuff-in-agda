import Structure.Logic.Classical.NaturalDeduction

module Structure.Logic.Classical.SetTheory.Relation {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic : _ ⦄ (_∈_ : Domain → Domain → Formula) where
open Structure.Logic.Classical.NaturalDeduction.ClassicalLogic {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} (classicLogic)

open import Syntax.Function
open import Structure.Logic.Classical.SetTheory.SetBoundedQuantification {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic ⦄ (_∈_)

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

-- Not element of
_∉_ : BinaryRelator
_∉_ x a = ¬(x ∈ a)

-- Subset of
_⊆_ : BinaryRelator
_⊆_ a b = ∀ₗ(x ↦ (x ∈ a) ⟶ (x ∈ b))

-- Superset of
_⊇_ : BinaryRelator
_⊇_ a b = ∀ₗ(x ↦ (x ∈ a) ⟵ (x ∈ b))

-- Equality of
_≡ₛ_ : BinaryRelator
_≡ₛ_ a b = ∀ₗ(x ↦ (x ∈ a) ⟷ (x ∈ b))

-- The statement that the set s is empty
Empty : UnaryRelator
Empty(s) = ∀ₗ(x ↦ ¬(x ∈ s))

-- The statement that the set s is non-empty
NonEmpty : UnaryRelator
NonEmpty(s) = ∃ₗ(x ↦ (x ∈ s))

-- The statement that the set s is a set that contains all sets
Universal : UnaryRelator
Universal(s) = ∀ₗ(x ↦ (x ∈ s))

-- The statement that the sets s₁ and s₂ are disjoint
Disjoint : BinaryRelator
Disjoint(s₁)(s₂) = ∀ₗ(x ↦ ¬((x ∈ s₁)∧(x ∈ s₂)))
-- ¬ ∃ₗ(x ↦ (x ∈ s₁)∧(x ∈ s₂))

-- The statement that the sets in ss are all pairwise disjoint
PairwiseDisjoint : UnaryRelator
PairwiseDisjoint(ss) = ∀ₛ(ss)(s₁ ↦ ∀ₛ(ss)(s₂ ↦ ∀ₗ(x ↦ (x ∈ s₁)∧(x ∈ s₂) ⟶ (s₁ ≡ s₂))))
-- ∀ₛ(ss)(s₁ ↦ ∀ₛ(ss)(s₂ ↦ (s₁ ≢ s₂) → Disjoint(s₁)(s₂)))

-- The statement that the relation predicate F can be interpreted as a partial function
PartialFunction : BinaryRelator → Domain → Formula
PartialFunction(F) (dom) = ∀ₛ(dom)(x ↦ Unique(y ↦ F(x)(y)))

-- The statement that the relation predicate F can be interpreted as a total function
TotalFunction : BinaryRelator → Domain → Formula
TotalFunction(F) (dom) = ∀ₛ(dom)(x ↦ ∃ₗ!(y ↦ F(x)(y)))

-- A binary relator modifier which makes the binary relator to a statement about all distinct pairs in a set.
-- Note: This is specifically for irreflexive binary relations.
Pairwise : BinaryRelator → UnaryRelator
Pairwise Related (S) = ∀ₛ(S)(a ↦ ∀ₛ(S)(b ↦ (a ≢ b) ⟶ Related(a)(b)))
