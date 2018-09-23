open import Logic.Classical.NaturalDeduction

module Logic.Classical.SetTheory.Relation {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} {Proof} ⦃ predicateEqTheory : PredicateEq.Theory{ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} (Proof) ⦄ (_∈_ : Domain → Domain → Stmt) where

open import Syntax.Function
open        Logic.Classical.NaturalDeduction.PredicateEq {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} (Proof) renaming (Theory to PredicateEqTheory)
open import Logic.Classical.SetTheory.BoundedQuantification ⦃ predicateEqTheory ⦄ (_∈_)

open        PredicateEqTheory (predicateEqTheory)

UnaryRelator : Set(_)
UnaryRelator = (Domain → Stmt)

BinaryRelator : Set(_)
BinaryRelator = (Domain → Domain → Stmt)

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
PartialFunction : BinaryRelator → Domain → Stmt
PartialFunction(F) (dom) = ∀ₛ(dom)(x ↦ Unique(y ↦ F(x)(y)))

-- The statement that the relation predicate F is a total function
TotalFunction : BinaryRelator → Domain → Stmt
TotalFunction(F) (dom) = ∀ₛ(dom)(x ↦ ∃ₗ!(y ↦ F(x)(y)))
