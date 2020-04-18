module Function.Inverse where

import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Functional
open import Function.Names using (_⊜_)
open import Function.Inverseᵣ
open import Structure.Setoid.WithLvl
open import Structure.Setoid.Uniqueness
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

module _ {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂} {A : Type{ℓ₁}} ⦃ eqA : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓ₂}} ⦃ eqB : Equiv{ℓₑ₂}(B) ⦄ where
  -- The inverse function of a bijective function f.
  inv : (f : A → B) → ⦃ _ : Bijective(f) ⦄ → (B → A)
  inv(f) = invᵣ(f) ⦃ bijective-to-surjective(f) ⦄

  module _ {f : A → B} ⦃ bij : Bijective(f) ⦄ where
    -- inv is a right inverse function to a bijective f.
    inv-inverseᵣ : (f ∘ inv(f) ⊜ id)
    inv-inverseᵣ = invᵣ-inverseᵣ ⦃ surj = bijective-to-surjective(f) ⦄

    -- inv is a left inverse function to a bijective f.
    inv-inverseₗ : (inv(f) ∘ f ⊜ id)
    inv-inverseₗ = [∃!]-existence-eq-any (bijective(f)) (reflexivity(_≡_))

    -- inv(f) is surjective when f is bijective.
    inv-surjective : Surjective(inv(f))
    Surjective.proof(inv-surjective) {x} = [∃]-intro(f(x)) ⦃ inv-inverseₗ ⦄

    inv-unique-inverseᵣ : ∀{f⁻¹} → (f ∘ f⁻¹ ⊜ id) → (f⁻¹ ⊜ inv(f))
    inv-unique-inverseᵣ = invᵣ-unique-inverseᵣ ⦃ surj = bijective-to-surjective(f) ⦄ ⦃ inj = bijective-to-injective(f) ⦄

    inv-unique-inverseₗ : ∀{f⁻¹} → ⦃ _ : Function(f⁻¹) ⦄ → (f⁻¹ ∘ f ⊜ id) → (f⁻¹ ⊜ inv(f))
    inv-unique-inverseₗ = invᵣ-unique-inverseₗ ⦃ surj = bijective-to-surjective(f) ⦄

    -- inv(f) is a function when f is a function.
    inv-function : Function(inv(f))
    inv-function = invᵣ-function ⦃ surj = bijective-to-surjective(f) ⦄ ⦃ inj = bijective-to-injective(f) ⦄

    module _ ⦃ func : Function(f) ⦄ where
      -- inv(f) is injective when f is a function and is bijective.
      inv-injective : Injective(inv f)
      inv-injective = invᵣ-injective ⦃ surj = bijective-to-surjective(f) ⦄

      -- inv(f) is bijective when f is a function and is bijective.
      inv-bijective : Bijective(inv(f))
      inv-bijective = injective-surjective-to-bijective(inv(f)) ⦃ inv-injective ⦄ ⦃ inv-surjective ⦄
