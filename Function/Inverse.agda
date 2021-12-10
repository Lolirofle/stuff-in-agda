module Function.Inverse where

open import Data.Tuple as Tuple using (_⨯_ ; _,_)
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Functional
open import Function.Equals
open import Function.Equals.Proofs
open import Function.Inverseₗ
open import Function.Inverseᵣ
open import Structure.Setoid
open import Structure.Setoid.Uniqueness
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

module _ {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂} {A : Type{ℓ₁}} ⦃ eqA : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓ₂}} ⦃ eqB : Equiv{ℓₑ₂}(B) ⦄ where
  private variable f : A → B

  -- The inverse function of a bijective function f.
  inv : (f : A → B) → ⦃ inver : Invertible(f) ⦄ → (B → A)
  inv(f) ⦃ inver ⦄ = [∃]-witness inver

  module _ {f : A → B} ⦃ inver : Invertible(f) ⦄ where
    inv-inverse : Inverse(f)(inv f)
    inv-inverse = [∧]-elimᵣ([∃]-proof inver)

    inv-inverseₗ : Inverseₗ(f)(inv f)
    inv-inverseₗ = [∧]-elimₗ inv-inverse

    inv-inverseᵣ : Inverseᵣ(f)(inv f)
    inv-inverseᵣ = [∧]-elimᵣ inv-inverse

    inv-function : Function(inv f)
    inv-function = [∧]-elimₗ([∃]-proof inver)

    inv-surjective : Surjective(inv f)
    inv-surjective = inverse-surjective ⦃ inver = [∧]-elimᵣ([∃]-proof inver) ⦄

    module _ ⦃ func : Function(f) ⦄ where
      inv-injective : Injective(inv f)
      inv-injective = inverse-injective ⦃ inver = [∧]-elimᵣ([∃]-proof inver) ⦄

      inv-bijective : Bijective(inv f)
      inv-bijective = inverse-bijective ⦃ inver = [∧]-elimᵣ([∃]-proof inver) ⦄

{-
  module _ {f : A → B} ⦃ inver : Invertible(f) ⦄ ⦃ inv-func : Function(inv f) ⦄ where
    inv-sides-equality : (invₗ(f) ⊜ invᵣ(f))
    inv-sides-equality =
      invₗ(f)                 🝖[ _⊜_ ]-[]
      invₗ(f) ∘ id            🝖[ _⊜_ ]-[ [⊜][∘]-binaryOperator-raw {f₁ = invₗ(f)} ⦃ func₂ = {!!} ⦄ (reflexivity(_⊜_)) (intro(inverseᵣ(f)(invᵣ f) ⦃ inv-inverseᵣ ⦄)) ]-sym
      invₗ(f) ∘ (f ∘ invᵣ(f)) 🝖[ _⊜_ ]-[]
      (invₗ(f) ∘ f) ∘ invᵣ(f) 🝖[ _⊜_ ]-[ {!!} ]
      id ∘ invᵣ(f)            🝖[ _⊜_ ]-[]
      invᵣ(f)                 🝖-end

-- congruence₂-₂(_∘_)(invₗ(f)) ?

    -- x₁ ≡ x₂
    -- inv f(y₁) ≡ inv f(y₂)

    --f(x₁) ≡ f(x₂)
    --invᵣ f(f(x₁)) ≡ invᵣ f(f(x₂))
    --invᵣ f(f(x₁))

-}













{-
    -- inv is a left inverse function to a bijective f.
    inv-inverseₗ : Inverseₗ(f)(inv f)
    inv-inverseₗ = invᵣ-inverseₗ ⦃ inj = {!invertibleₗ-to-injective!} ⦄
    -- [∃!]-existence-eq-any (bijective(f)) (reflexivity(_≡_))

    inv-injective : Injective(inv f)
    inv-injective = {!invᵣ-injective!}-}


{-
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
-}
