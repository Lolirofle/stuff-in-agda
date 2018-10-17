open import Structure.Logic.Classical.NaturalDeduction

-- TODO: This file is unused at the moment because I couldn't find a good way to prove stuff here without extentionality, and if one assumes it, then this file becomes kind of specific to the model ZF? If that would be the case, then there is no point in this
module Structure.Logic.Classical.SetTheory {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Formula} {Domain} {Proof} ⦃ predicateEqTheory : PredicateEq.Theory{ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Formula} {Domain} (Proof) ⦄ (_∈_ : Domain → Domain → Formula) where

import      Lvl
open import Syntax.Function
open        Structure.Logic.Classical.NaturalDeduction.PredicateEq {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Formula} {Domain} (Proof) renaming (Theory to PredicateEqTheory)
open import Structure.Logic.Classical.SetTheory.Relation ⦃ predicateEqTheory ⦄ (_∈_)
open import Type

open        PredicateEqTheory (predicateEqTheory)

record SetEquality : Type{ℓₘₗ Lvl.⊔ ℓₘₒ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  field
    _≡ₛ_ : Domain → Domain → Formula

  field
    definition : Proof(∀ₗ(s₁ ↦ ∀ₗ(s₂ ↦ ∀ₗ(x ↦ (x ∈ s₁) ⟷ (x ∈ s₂)) ⟷ (s₁ ≡ₛ s₂))))

-- Empty set
-- The set consisting of no elements.
record EmptySet : Type{ℓₘₗ Lvl.⊔ ℓₘₒ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  field
    ∅ : Domain

  field
    inclusion : Proof(∀ₗ(x ↦ x ∉ ∅))

-- Subset filtering.
-- The subset of the specified set where all elements satisfy the specified formula.
record FilterSet : Type{ℓₘₗ Lvl.⊔ ℓₘₒ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  field
    filter : Domain → (Domain → Formula) → Domain

-- Power set.
-- The set of all subsets of the specified set.
record PowerSet : Type{ℓₘₗ Lvl.⊔ ℓₘₒ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  field
    ℘ : Domain → Domain

-- Union over arbitrary sets.
-- Constructs a set which consists of elements which are in any of the specified sets.
record SetUnionSet : Type{ℓₘₗ Lvl.⊔ ℓₘₒ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  field
    ⋃ : Domain → Domain

-- Singleton set.
-- A set consisting of only a single element.
record SingletonSet : Type{ℓₘₗ Lvl.⊔ ℓₘₒ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  field
    singleton : Domain → Domain

-- Union operator.
-- Constructs a set which consists of both elements from LHS and RHS.
record UnionSet : Type{ℓₘₗ Lvl.⊔ ℓₘₒ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  field
    _∪_ : Domain → Domain → Domain

-- Intersection operator.
-- Constructs a set which consists of elements which are in both LHS and RHS.
record IntersectionSet : Type{ℓₘₗ Lvl.⊔ ℓₘₒ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  field
    _∩_ : Domain → Domain → Domain

-- "Without"-operator.
-- Constructs a set which consists of elements which are in LHS, but not RHS.
record WithoutSet : Type{ℓₘₗ Lvl.⊔ ℓₘₒ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  field
    _∖_ : Domain → Domain → Domain

-- Intersection over arbitrary sets.
-- Constructs a set which consists of elements which are in all of the specified sets.
record SetIntersectionSet : Type{ℓₘₗ Lvl.⊔ ℓₘₒ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  field
    ⋂ : Domain → Domain

record TupleSet : Type{ℓₘₗ Lvl.⊔ ℓₘₒ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  field
    -- Set product (Set of tuples) (Cartesian product).
    _⨯_ : Domain → Domain → Domain

    -- Tuple value.
    -- An ordered pair of values.
    _,_ : Domain → Domain → Domain

record QuotientSet : Type{ℓₘₗ Lvl.⊔ ℓₘₒ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  field
    -- Quotient set.
    -- The set of equivalence classes.
    _/_ : Domain → BinaryRelator → Domain

    -- Equivalence class
    -- The set of elements which are equivalent to the specified one.
    [_of_,_] : Domain → Domain → BinaryRelator → Domain
