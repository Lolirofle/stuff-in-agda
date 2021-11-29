module Structure.Relator.Ordering.Proofs where

import      Lvl
open import Functional
open import Functional.Instance
open import Logic
open import Structure.Relator
open import Structure.Relator.Proofs
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Structure.Relator.Properties.Proofs
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T A B : Type{ℓ}
private variable _≤_ _≤₁_ _≤₂_ : A → A → Stmt{ℓ}
private variable f : A → B
private variable x : A

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ ord : Weak.PartialOrder{T = T}(_≤_) ⦄ where
  [≡][≤]-sub : (_≡_) ⊆₂ (_≤_)
  _⊆₂_.proof [≡][≤]-sub = apply (reflexivity(_≤_)) ∘ substitute₂ᵣ(_≤_)

module _ ⦃ trans : Transitivity{T = B}(_≤_) ⦄ where
  open Strict.Properties

  -- TODO: Agda bug 20200523 does not allow instance arg
  accessibleₗ-image-by-trans : Accessibleₗ{T = B}(_≤_)(f(x)) → Accessibleₗ((_≤_) on₂ f)(x)
  accessibleₗ-image-by-trans {f = f} {y} (intro ⦃ acc ⦄) = intro ⦃ \{x} ⦃ xy ⦄ → intro ⦃ \{a} ⦃ ax ⦄ → accessibleₗ-image-by-trans (acc {f(a)} ⦃ transitivity(_≤_) ax xy ⦄ ) ⦄ ⦄

  wellfounded-image-by-trans : ∀{f : A → B} → ⦃ _ : WellFounded{T = B}(_≤_) ⦄ → WellFounded((_≤_) on₂ f)
  wellfounded-image-by-trans = accessibleₗ-image-by-trans infer

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

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  swap-weakPartialOrder : ⦃ ord : Weak.PartialOrder{T = T}(_≤_) ⦄ → Weak.PartialOrder(swap(_≤_))
  Weak.PartialOrder.relator      swap-weakPartialOrder = swap-binaryRelator
  Weak.PartialOrder.antisymmetry swap-weakPartialOrder = swap-antisymmetry
  Weak.PartialOrder.transitivity swap-weakPartialOrder = swap-transitivity
  Weak.PartialOrder.reflexivity  swap-weakPartialOrder = swap-reflexivity

  swap-weakTotalOrder : ⦃ ord : Weak.TotalOrder{T = T}(_≤_) ⦄ → Weak.TotalOrder(swap(_≤_))
  Weak.TotalOrder.partialOrder swap-weakTotalOrder = swap-weakPartialOrder
  Weak.TotalOrder.totality     swap-weakTotalOrder = swap-converseTotal

  swap-strictPartialOrder : ⦃ ord : Strict.PartialOrder{T = T}(_≤_) ⦄ → Strict.PartialOrder(swap(_≤_))
  Strict.PartialOrder.relator       swap-strictPartialOrder = swap-binaryRelator
  Strict.PartialOrder.transitivity  swap-strictPartialOrder = swap-transitivity
  Strict.PartialOrder.asymmetry     swap-strictPartialOrder = swap-asymmetry
  Strict.PartialOrder.irreflexivity swap-strictPartialOrder = swap-irreflexivity

  swap-strictTotalOrder : ⦃ ord : Strict.TotalOrder{T = T}(_≤_) ⦄ → Strict.TotalOrder(swap(_≤_))
  Strict.TotalOrder.partialOrder swap-strictTotalOrder = swap-strictPartialOrder
  Strict.TotalOrder.trichotomy   swap-strictTotalOrder = swap-converseTrichotomy
