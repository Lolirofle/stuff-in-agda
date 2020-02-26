module Structure.Relator.Ordering.Proofs where

import      Lvl
open import Functional
open import Logic
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ : Lvl.Level
private variable A B : Type{ℓ}
private variable _≤_ _≤₁_ _≤₂_ : A → A → Stmt{ℓ}
private variable f : A → B
private variable x : A

module _ ⦃ trans : Transitivity{T = B}(_≤_) ⦄ where
  open Strict.Properties

  accessibleₗ-image-by-trans : ⦃ _ : Accessibleₗ{T = B}(_≤_)(f(x)) ⦄ → Accessibleₗ((_≤_) on₂ f)(x)
  Accessibleₗ.proof (accessibleₗ-image-by-trans {f = f} {y} ⦃ intro ⦃ acc ⦄ ⦄) {x} ⦃ xy ⦄ = intro ⦃ \{a} ⦃ ax ⦄ → accessibleₗ-image-by-trans ⦃ acc {f(a)} ⦃ transitivity(_≤_) ax xy ⦄ ⦄ ⦄

  wellfounded-image-by-trans : ∀{f : A → B} → ⦃ _ : WellFounded{T = B}(_≤_) ⦄ → WellFounded((_≤_) on₂ f)
  wellfounded-image-by-trans = accessibleₗ-image-by-trans

module _ ⦃ refl : Reflexivity{T = B}(_≤_) ⦄ where
  open Strict.Properties

  accessibleₗ-image-by-refl : ⦃ _ : Accessibleₗ{T = B}(_≤_)(f(x)) ⦄ → Accessibleₗ((_≤_) on₂ f)(x)
  accessibleₗ-image-by-refl {f = f} {y} ⦃ intro ⦃ acc ⦄ ⦄ = accessibleₗ-image-by-refl ⦃ acc{f(y)} ⦃ reflexivity(_≤_) ⦄ ⦄

  wellfounded-image-by-refl : ∀{f : A → B} → ⦃ _ : WellFounded{T = B}(_≤_) ⦄ → WellFounded((_≤_) on₂ f)
  wellfounded-image-by-refl = accessibleₗ-image-by-refl

module _ ⦃ sub : (_≤₁_) ⊆₂ (_≤₂_) ⦄ where
  open Strict.Properties

  accessibleₗ-sub₂ : ⦃ _ : Accessibleₗ(_≤₂_)(x) ⦄ → Accessibleₗ(_≤₁_)(x)
  accessibleₗ-sub₂ {x = y} ⦃ intro ⦃ acc ⦄ ⦄ = intro ⦃ \{x} ⦃ xy ⦄ → accessibleₗ-sub₂ ⦃ acc{x} ⦃ sub₂(_≤₁_)(_≤₂_) xy ⦄ ⦄ ⦄

  wellfounded-sub₂ : ⦃ _ : WellFounded(_≤₂_) ⦄ → WellFounded(_≤₁_)
  wellfounded-sub₂ = accessibleₗ-sub₂
