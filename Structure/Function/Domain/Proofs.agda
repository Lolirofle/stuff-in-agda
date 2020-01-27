module Structure.Function.Domain.Proofs where

import      Lvl
open import Functional
import      Function.Names as Names
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid hiding (Function)
open import Sets.Setoid.Uniqueness
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

module _ {ℓₒ₁}{ℓₒ₂} {A : Type{ℓₒ₁}} ⦃ _ : Equiv(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ (f : A → B) where
  injective-to-unique : Injective(f) → ∀{y} → Unique(x ↦ f(x) ≡ y)
  injective-to-unique (intro(inj)) {y} {x₁}{x₂} fx₁y fx₂y =
    inj{x₁}{x₂} (fx₁y 🝖 symmetry(_≡_) fx₂y)

  instance
    bijective-to-injective : ⦃ _ : Bijective(f) ⦄ → Injective(f)
    Injective.proof(bijective-to-injective ⦃ intro(bij) ⦄) {x₁}{x₂} (fx₁fx₂) =
      ([∃!]-existence-eq (bij {f(x₂)}) {x₁} (fx₁fx₂))
      🝖 symmetry(_≡_) ([∃!]-existence-eq (bij {f(x₂)}) {x₂} (reflexivity(_≡_)))
    -- ∀{y : B} → ∃!(x ↦ f(x) ≡ y)
    -- ∃!(x ↦ f(x) ≡ f(x₂))
    -- ∀{x} → (f(x) ≡ f(x₂)) → (x ≡ [∃!]-witness e)
    -- (f(x₁) ≡ f(x₂)) → (x₁ ≡ [∃!]-witness e)
    --
    -- ∀{y : B} → ∃!(x ↦ f(x) ≡ y)
    -- ∃!(x ↦ f(x) ≡ f(x₂))
    -- ∀{x} → (f(x) ≡ f(x₂)) → (x ≡ [∃!]-witness e)
    -- (f(x₂) ≡ f(x₂)) → (x₂ ≡ [∃!]-witness e)

  instance
    bijective-to-surjective : ⦃ _ : Bijective(f) ⦄ → Surjective(f)
    Surjective.proof(bijective-to-surjective ⦃ intro(bij) ⦄) {y} =
      [∃!]-existence (bij {y})

  instance
    injective-surjective-to-bijective : ⦃ _ : Injective(f) ⦄ → ⦃ _ : Surjective(f) ⦄ → Bijective(f)
    Bijective.proof(injective-surjective-to-bijective ⦃ inj ⦄ ⦃ intro(surj) ⦄) {y} =
      [∃!]-intro surj (injective-to-unique inj)
