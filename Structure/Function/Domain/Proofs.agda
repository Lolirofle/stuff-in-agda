module Structure.Function.Domain.Proofs where

import      Lvl
open import Functional
open import Function.Domains
open import Function.Equals
import      Function.Names as Names
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid
open import Sets.Setoid.Uniqueness
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓₒ₁ ℓₒ₂ : Lvl.Level

module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ (f : A → B) where
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

module _ {A : Type{ℓₒ₁}} ⦃ equiv-A : Equiv(A) ⦄ {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv(B) ⦄ where
  instance
    injective-relator : UnaryRelator(Injective{A = A}{B = B})
    Injective.proof (UnaryRelator.substitution injective-relator {f₁}{f₂} (intro f₁f₂) (intro inj-f₁)) f₂xf₂y = inj-f₁ (f₁f₂ 🝖 f₂xf₂y 🝖 symmetry(_≡_) f₁f₂)

module _ {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv(B) ⦄ where
  instance
    surjective-relator : UnaryRelator(Surjective{A = A}{B = B})
    Surjective.proof (UnaryRelator.substitution surjective-relator {f₁}{f₂} (intro f₁f₂) (intro surj-f₁)) {y} = [∃]-map-proof (\{x} f₁xf₁y → symmetry(_≡_) (f₁f₂{x}) 🝖 f₁xf₁y) (surj-f₁{y})
