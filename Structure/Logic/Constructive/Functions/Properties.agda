module Structure.Logic.Constructive.Functions.Properties {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Formula} {Domain} {Proof} ⦃ predicateEqTheory : PredicateEq.Theory{ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Formula} {Domain} (Proof) ⦄ where

open import Lang.Instance
import      Lvl
open        Structure.Logic.Constructive.NaturalDeduction.PredicateEq {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Formula} {Domain} (Proof) renaming (Theory to PredicateEqTheory)

open        PredicateEqTheory (predicateEqTheory)

-- States whether the function f is defined on the element x.
-- Whether f(x) yields/returns an element in the domain.
-- In other words: Whether the logic can interpret f(x) as anything meaningful.
Defined : Function → Domain → Formula
Defined f(x) = ∃ₗ(y ↦ f(x) ≡ y)

-- States whether the function f can yield/return the element y.
Value : Function → Domain → Formula
Value f(y) = ∃ₗ(x ↦ f(x) ≡ y)

Injective : Function → Formula
Injective(f) = ∀ₗ(x ↦ ∀ₗ(y ↦ (f(x) ≡ f(y)) ⟶ (x ≡ y)))

Surjective : Domain → Domain → Function → Formula
Surjective(f) = ∀ₗ(y ↦ ∃ₗ(x ↦ f(x) ≡ y))

Bijective : Domain → Domain → Function → Formula
Bijective(f) =
  Injective(f)
  ∧ Surjective(f)

Preserving₁ : Domain → Function → Function → Function → Formula
Preserving₁(f)(g₁)(g₂) = ∀ₗ(x ↦ f(g₁(x)) ≡ g₂(f(x)))

Preserving₂ : Domain → Domain → Function → BinaryOperator → BinaryOperator → Formula
Preserving₂(f)(_▫₁_)(_▫₂_) = ∀ₗ(x ↦ ∀ₗ(y ↦ f(x ▫₁ y) ≡ (f(x) ▫₂ f(y))))

Fixpoint : Function → Domain → Formula
Fixpoint f(x) = (f(x) ≡ x)
