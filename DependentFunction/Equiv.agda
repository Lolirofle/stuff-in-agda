module DependentFunction.Equiv where

open import Function.Names
open import Functional using (_→ᶠ_)
open import DependentFunctional using (_$_ ; pointwise₂,₂)
open import DependentFunction using ()
open import Logic.Predicate
open import Logic.Propositional
open import Logic
import      Lvl
open import Structure.Function
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ₁ ℓₑ₂ ℓₑ : Lvl.Level
private variable A : Type{ℓ}
private variable B : A → Type{ℓ}

FunctionExtensionality : ⦃ equiv-B : ∀{a : A} → Equiv{ℓₑ₂}(B(a)) ⦄ → (((a : A) → B(a)) → ((a : A) → B(a)) → Type{ℓₑ}) → Type
FunctionExtensionality{A = A}{B = B}(_≡_) = ∀²(pointwise₂,₂(_→ᶠ_) (_⊜_)(_≡_))

-- An equivalence on functions is correct when it behaves like the pointwise function equivalence.
record Extensionality (equiv-B : ∀{a : A} → Equiv{ℓₑ₂}(B(a))) (equiv : Equiv{ℓₑ}((a : A) → B(a))) : Type{Lvl.of((a : A) → B(a)) Lvl.⊔ ℓₑ₂ Lvl.⊔ ℓₑ} where
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
  using    (functionExtensionality ; apply-fn-function)
  renaming (pointwise to pointwiseEquality)
