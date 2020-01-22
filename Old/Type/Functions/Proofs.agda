import Lvl

module Type.Functions.Proofs {ℓₗ : Lvl.Level} where

open import Functional
import      Function.Domains
import      Lang.Irrelevance
import      Logic.Predicate
import      Logic.Predicate.Theorems
import      Relator.Equals
import      Relator.Equals.Proofs
open import Type
open import Type.Empty
import      Type.Functions
import      Type.Singleton.Proofs
open import Type.Unit
open import Type.Unit.Proofs

module _ {ℓₒ₁}{ℓₒ₂} {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} {f : X → Y} where
  open Type.Functions {ℓₗ}{ℓₒ₁}{ℓₒ₂} {X}{Y}

  bijective-to-injective : ⦃ _ : Bijective(f) ⦄ → Injective(f)
  Injective.proof (bijective-to-injective ⦃ intro proof ⦄) {y} =
    unit-is-prop {ℓₒ₁} ⦃ proof{y} ⦄

  bijective-to-surjective : ⦃ _ : Bijective(f) ⦄ → Surjective(f)
  Surjective.proof (bijective-to-surjective ⦃ intro proof ⦄) {y} =
    unit-is-pos {ℓₗ Lvl.⊔ ℓₒ₁} ⦃ proof{y} ⦄

  injective-surjective-to-bijective : ⦃ _ : Injective(f) ⦄ → ⦃ _ : Surjective(f) ⦄ → Bijective(f)
  Bijective.proof(injective-surjective-to-bijective ⦃ intro inj ⦄ ⦃ intro surj ⦄) {y} =
    pos-prop-is-unit {ℓₗ Lvl.⊔ ℓₒ₁} ⦃ surj{y} ⦄ ⦃ inj{y} ⦄

module _ {ℓₒ₁}{ℓₒ₂} {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} {f : X → Y} where
  open Function.Domains
  open Type.Functions {ℓₗ}{ℓₒ₁}{ℓₒ₂} {X}{Y}
  open Relator.Equals

  private
    _≡₁_ = _≡_ {ℓₗ Lvl.⊔ ℓₒ₁}

  Injective-apply : ⦃ _ : Injective(f) ⦄ → ∀{x y} → (f(x) ≡₁ f(y)) → (x ≡₁ y)
  Injective-apply ⦃ Injective.intro proof ⦄ {x}{y} (fxfy) with proof{f(y)}
  ... | IsProp.intro uniqueness with uniqueness{Unapply.intro x ⦃ fxfy ⦄} {Unapply.intro y ⦃ [≡]-intro ⦄}
  ...   | [≡]-intro = [≡]-intro

module _ {ℓₒ : Lvl.Level} {X : Type{ℓₒ}} where
  open Type.Functions {ℓₗ Lvl.⊔ ℓₒ}{ℓₒ}{ℓₒ} {X}{X}
  open Type.Singleton.Proofs {ℓₗ}{ℓₒ} {X}

  instance
    id-is-bijective : Bijective(id)
    id-is-bijective = intro Singleton-is-unit
