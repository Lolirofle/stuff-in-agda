open import Functional using (id)
import      Structure.Logic.Constructive.NaturalDeduction

module Structure.Logic.Constructive.Functions.Properties {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ constructiveLogicSign : _ ⦄ where
open Structure.Logic.Constructive.NaturalDeduction.ConstructiveLogicSignature {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} (constructiveLogicSign)

open import Structure.Logic.Constructive.Functions(Domain)
open import Syntax.Function

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

Surjective : Function → Formula
Surjective(f) = ∀ₗ(y ↦ ∃ₗ(x ↦ f(x) ≡ y))

Bijective : Function → Formula
Bijective(f) =
  Injective(f)
  ∧ Surjective(f)

Preserving₁ : Function → Function → Function → Formula
Preserving₁(f)(g₁)(g₂) = ∀ₗ(x ↦ f(g₁(x)) ≡ g₂(f(x)))

Preserving₂ : Function → BinaryOperator → BinaryOperator → Formula
Preserving₂(f)(_▫₁_)(_▫₂_) = ∀ₗ(x ↦ ∀ₗ(y ↦ f(x ▫₁ y) ≡ (f(x) ▫₂ f(y))))

Fixpoint : Function → Domain → Formula
Fixpoint f(x) = (f(x) ≡ x)
