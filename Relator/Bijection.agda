module Relator.Bijection {ℓ₁} {ℓ₂} where

import      Lvl
open import Functional
open import Functional.Proofs
open import Logic.Propositional
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals.Proofs{ℓ₁}
open import Structure.Function.Domain{ℓ₁}
open import Structure.Relator.Properties{ℓ₁}
open import Type{ℓ₂}

-- TODO: Merge with Cardinality, Functional.Domains, and Functional.Proofs

-- A bijection between the types {A,B} means that (∃(f: A → B). Bijective(f)) is satisfied.
data Bijection (T₁ : Type) (T₂ : Type) : Stmt{ℓ₁ Lvl.⊔ Lvl.𝐒(ℓ₂)} where
  bijection-intro : (f : T₁ → T₂) → Bijective(f) → Bijection(T₁)(T₂)

module _ (T₁ : Type) (T₂ : Type) where
  Bijection-fn : ⦃ _ : Bijection(T₁)(T₂) ⦄ → T₁ → T₂
  Bijection-fn ⦃ bijection-intro f (_) ⦄ = f

  Bijection-inverse-fn : ⦃ _ : Bijection(T₁)(T₂) ⦄ → T₂ → T₁
  Bijection-inverse-fn ⦃ bijection-intro f ([∧]-intro injective surjective) ⦄ =
    (y ↦ [∃]-witness(surjective{y}))

  postulate Bijection-inverseᵣ : ⦃ _ : Bijection(T₁)(T₂) ⦄ → ∀{y : T₂} → ((Bijection-fn ∘ Bijection-inverse-fn)(y) ≡ y)

-- TODO
inverse : ∀{T₁ T₂} → Bijection(T₁)(T₂) → Bijection(T₂)(T₁)
inverse{T₁}{T₂} (bijection @ (bijection-intro f ([∧]-intro inj-f surj-f))) =
  bijection-intro f⁻¹ ([∧]-intro inj-f⁻¹ surj-f⁻¹) where
    f⁻¹ = Bijection-inverse-fn(T₁)(T₂) ⦃ bijection ⦄

    inj-f⁻¹ : Injective(f⁻¹)
    inj-f⁻¹ {y₁}{y₂} (f⁻¹y₁≡f⁻¹y₂) =
      (symmetry (Bijection-inverseᵣ(T₁)(T₂) ⦃ bijection ⦄ {y₁}))
      🝖 [≡]-with(f) (f⁻¹y₁≡f⁻¹y₂)
      🝖 Bijection-inverseᵣ(T₁)(T₂) ⦃ bijection ⦄ {y₂}
      where
        x₁ = f⁻¹(y₁)
        x₂ = f⁻¹(y₂)

    postulate surj-f⁻¹ : Surjective(f⁻¹)
    -- (\{x} → [∃]-intro(f(x)))

instance
  Bijection-reflexivity : Reflexivity{Lvl.𝐒(ℓ₂)}(Bijection)
  reflexivity ⦃ Bijection-reflexivity ⦄ = bijection-intro(id)(id-bijective)

instance
  Bijection-symmetry : Symmetry{Lvl.𝐒(ℓ₂)}(Bijection)
  symmetry ⦃ Bijection-symmetry ⦄ (bijection) = inverse(bijection)

-- TODO: Use function composition and other compositions in some way
instance
  postulate Bijection-transitivity : Transitivity{Lvl.𝐒(ℓ₂)}(Bijection)
--   Bijection-transitivity([∧]-intro [≡]-intro [≡]-intro) = [≡]-intro
