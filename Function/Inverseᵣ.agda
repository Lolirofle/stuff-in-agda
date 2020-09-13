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

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable A B : Type{ℓ}

module _
  {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  where

  private variable f : A → B

  invᵣ : (f : A → B) → ⦃ inverᵣ : Invertibleᵣ(f) ⦄ → (B → A)
  invᵣ f ⦃ inverᵣ ⦄ = [∃]-witness inverᵣ

module _
  {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {f : A → B} ⦃ inverᵣ : Invertibleᵣ(f) ⦄
  where

  -- `invᵣ f` is a right inverse of `f` for `(_∘_)`.
  invᵣ-inverseᵣ : Inverseᵣ(f)(invᵣ(f))
  invᵣ-inverseᵣ = [∧]-elimᵣ([∃]-proof inverᵣ)

module _
  {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {f : A → B} ⦃ func : Function(f) ⦄ ⦃ inj : Injective(f) ⦄ ⦃ inverᵣ : Invertibleᵣ(f) ⦄
  where

  invᵣ-invertible : Invertibleᵣ(invᵣ f)
  invᵣ-invertible = inverseᵣ-invertibleᵣ {f = f} {f⁻¹ = invᵣ(f)} ⦃ inverᵣ = invᵣ-inverseᵣ ⦄

  invᵣ-involution : (invᵣ(invᵣ(f)) ⦃ inverseᵣ-invertibleᵣ ⦃ inverᵣ = [∧]-elimᵣ([∃]-proof inverᵣ) ⦄ ⦄ ⊜ f)
  invᵣ-involution {x} =
    injective(invᵣ f) ⦃ inverseᵣ-injective ⦃ equiv-A = equiv-A ⦄ ⦃ equiv-B = equiv-B ⦄ {f = f} ⦄ $
      (invᵣ(f) ∘ invᵣ(invᵣ f))(x) 🝖[ _≡_ ]-[ inverseᵣ(invᵣ f)(invᵣ(invᵣ f)) ⦃ invᵣ-inverseᵣ ⦄ ]
      x                           🝖[ _≡_ ]-[ inverseₗ(f)(invᵣ f) ⦃ inverseᵣ-inverseₗ ⦄ ]-sym
      invᵣ f(f(x))                🝖-end
    where
      instance _ = [∧]-elimᵣ([∃]-proof(inverᵣ))
      instance _ = invᵣ-invertible
      instance _ = [∧]-elimᵣ([∃]-proof(invᵣ-invertible))

