module Function.Inverseᵣ where

import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Functional
open import Function.Names using (_⊜_)
open import Structure.Setoid.WithLvl
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

module _ {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂} {A : Type{ℓ₁}} ⦃ eqA : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓ₂}} ⦃ eqB : Equiv{ℓₑ₂}(B) ⦄ where
  module _ where
    -- One of the right inverse functions of a surjective function f.
    -- Specifically the one that is used in the constructive proof of surjectivity for f.
    invᵣ : (f : A → B) → ⦃ surj : Surjective(f) ⦄ → (B → A)
    invᵣ f(y) = [∃]-witness(surjective(f) {y})

    module _ {f : A → B} ⦃ surj : Surjective(f) ⦄ where
      -- The right inverse is a right inverse for the surjective f.
      invᵣ-inverseᵣ : (f ∘ invᵣ(f) ⊜ id)
      invᵣ-inverseᵣ{y} = [∃]-proof(surjective(f) {y})


    -- Every surjective function has a right inverse with respect to function composition.
    -- Note: Equivalent to axiom of choice from set theory when formulated in classical logic using the usual equality.
      [∘]-inverseᵣ : ⦃ _ : Surjective(f) ⦄ → ∃(g ↦ (f ∘ g ⊜ id))
      [∘]-inverseᵣ = [∃]-intro(invᵣ f) ⦃ invᵣ-inverseᵣ ⦄

      -- Note: This states that a function which is injective and surjective (bijective) is a function, but another way of satisfying this proposition is from a variant of axiom of choice which directly state that the right inverse of a surjective function always exist.
      invᵣ-function : ⦃ inj : Injective(f) ⦄ → Function(invᵣ f)
      Function.congruence invᵣ-function {y₁}{y₂} y₁y₂ with surjective(f){y₁} | surjective(f){y₂}
      ... | [∃]-intro x₁ ⦃ proof₁ ⦄ | [∃]-intro x₂ ⦃ proof₂ ⦄ =
        (injective(f) (
          f(x₁) 🝖-[ proof₁ ]
          y₁    🝖-[ y₁y₂ ]
          y₂    🝖-[ proof₂ ]-sym
          f(x₂) 🝖-end
        ))

      -- The right inverse is injective when f is a surjective function.
      invᵣ-injective : ⦃ func : Function(f) ⦄ → Injective(invᵣ f)
      Injective.proof(invᵣ-injective) {x₁}{x₂} (invᵣfx₁≡invᵣfx₂) =
        symmetry(_≡_) (invᵣ-inverseᵣ{x₁})
        🝖 congruence₁(f) {invᵣ f(x₁)} {invᵣ f(x₂)} (invᵣfx₁≡invᵣfx₂)
        🝖 invᵣ-inverseᵣ{x₂}

      -- The right inverse is surjective when the surjective f is injective.
      invᵣ-surjective : ⦃ inj : Injective(f) ⦄ → Surjective(invᵣ f)
      ∃.witness (Surjective.proof invᵣ-surjective {x}) = f(x)
      ∃.proof   (Surjective.proof invᵣ-surjective {x}) =
        injective(f) (
          f(invᵣ f(f(x))) 🝖-[ invᵣ-inverseᵣ ]
          f(x)            🝖-end
        )

      -- The right inverse is a left inverse when the surjective f is injective.
      invᵣ-inverseₗ : ⦃ inj : Injective(f) ⦄ → (invᵣ(f) ∘ f ⊜ id)
      invᵣ-inverseₗ = [∃]-proof(surjective(invᵣ(f)) ⦃ invᵣ-surjective ⦄)

      -- The right inverse is an unique right inverse when f is injective.
      invᵣ-unique-inverseᵣ : ⦃ inj : Injective(f) ⦄ → ∀{f⁻¹} → (f ∘ f⁻¹ ⊜ id) → (f⁻¹ ⊜ invᵣ(f))
      invᵣ-unique-inverseᵣ {f⁻¹} p {x} =
        f⁻¹(x)            🝖-[ invᵣ-inverseₗ ]-sym
        invᵣ f(f(f⁻¹(x))) 🝖-[ congruence₁(invᵣ f) ⦃ invᵣ-function ⦄ p ]
        invᵣ f(x)         🝖-end

      -- The right inverse is an unique left inverse function.
      invᵣ-unique-inverseₗ : ∀{f⁻¹} → ⦃ _ : Function(f⁻¹) ⦄ → (f⁻¹ ∘ f ⊜ id) → (f⁻¹ ⊜ invᵣ(f))
      invᵣ-unique-inverseₗ {f⁻¹} p {x} =
        f⁻¹(x)            🝖-[ congruence₁(f⁻¹) (symmetry(_≡_) invᵣ-inverseᵣ) ]
        f⁻¹(f(invᵣ f(x))) 🝖-[ p{invᵣ f(x)} ]
        invᵣ f(x)         🝖-end

      -- TODO: invᵣ-unique-function : ∀{g} → (invᵣ(f) ∘ g ⊜ id) → (g ⊜ f)

      -- The right inverse is bijective when the surjective f is injective.
      invᵣ-bijective : ⦃ func : Function(f) ⦄ → ⦃ inj : Injective(f) ⦄ → Bijective(invᵣ f)
      invᵣ-bijective = injective-surjective-to-bijective(invᵣ f) ⦃ invᵣ-injective ⦄ ⦃ invᵣ-surjective ⦄

{-
module _ {ℓ₁ ℓ₂} {A : Type{ℓ₁}} ⦃ eqA : Equiv(A) ⦄ {B : Type{ℓ₂}} ⦃ eqB : Equiv(B) ⦄ where
  module _ {f : A → B} ⦃ inj : Injective(f) ⦄ ⦃ surj : Surjective(f) ⦄ where
    invᵣ-involution : (invᵣ(invᵣ(f) ⦃ surj ⦄) ⦃ invᵣ-surjective ⦃ surj = surj ⦄ ⦃ inj = inj ⦄ ⦄ ⊜ f)
    invᵣ-involution {x} = {!!}
    -- invᵣ(invᵣ f)(x)
    -- f(invᵣ f(f(x)))
    -- f(x)
-}
