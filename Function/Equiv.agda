module Function.Equiv where

import      DependentFunction.Equiv as DepFnEquiv
import      Lvl
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ₁ ℓₑ₂ ℓₑ : Lvl.Level
private variable A B : Type{ℓ}

FunctionExtensionality : ⦃ equiv-B : let _ = A in Equiv{ℓₑ₂}(B) ⦄ → ((A → B) → (A → B) → Type{ℓₑ}) → Type
FunctionExtensionality = DepFnEquiv.FunctionExtensionality

Extensionality : (let _ = A in Equiv{ℓₑ₂}(B)) → (equiv : Equiv{ℓₑ}(A → B)) → Type
Extensionality equiv-B equiv = DepFnEquiv.Extensionality equiv-B equiv
module Extensionality {ℓ₁ ℓ₂ ℓₑ₂ ℓₑ}{A : Type{ℓ₁}}{B : Type{ℓ₂}} {equiv-B : Equiv{ℓₑ₂}(B)} {equiv : Equiv{ℓₑ}(A → B)} = DepFnEquiv.Extensionality {equiv-B = equiv-B} {equiv = equiv}

open Extensionality ⦃ … ⦄ public
  using    (functionExtensionality ; apply-fn-function)
  renaming (pointwise to pointwiseEquality)

open DepFnEquiv public
  using (intro)

{-
open import Function.Names
open import Functional
open import Logic.Predicate
open import Logic.Propositional
open import Logic
import      Lvl
open import Structure.Function
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ₁ ℓₑ₂ ℓₑ : Lvl.Level
private variable A B : Type{ℓ}

FunctionExtensionality : ⦃ equiv-B : let _ = A in Equiv{ℓₑ₂}(B) ⦄ → ((A → B) → (A → B) → Type{ℓₑ}) → Type
FunctionExtensionality(_≡_) = ∀²(pointwise₂,₂(_→ᶠ_) (_⊜_)(_≡_))

-- An equivalence on functions is correct when it behaves like the pointwise function equivalence.
record Extensionality (equiv-B : let _ = A in Equiv{ℓₑ₂}(B)) (equiv : Equiv{ℓₑ}(A → B)) : Type{Lvl.of(A)Lvl.⊔ Lvl.of(B) Lvl.⊔ ℓₑ₂ Lvl.⊔ ℓₑ} where
  constructor intro
  private instance _ = equiv
  private instance _ = equiv-B
  field pointwise : ∀²(pointwise₂,₂(_↔_) (_⊜_)(_≡_ ⦃ equiv ⦄))

  instance
    apply-fn-function : ∀{x : A} → Function(_$ x)
    Function.congruence apply-fn-function fg = [↔]-to-[←] pointwise fg

  functionExtensionality : FunctionExtensionality(_≡_)
  functionExtensionality = [↔]-to-[→] pointwise
open Extensionality ⦃ … ⦄ public
  using    (functionExtensionality)
  renaming (pointwise to pointwiseEquality)
-}
