open import Structure.Operator.Monoid
open import Structure.Setoid
open import Type

module Operator.Summation2 {ℓᵣ ℓ ℓₑ} (Range : Type{ℓᵣ}) {T : Type{ℓ}} (_▫_ : T → T → T) ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where

open import Functional using (_on₂_)
import      Lvl
open import Structure.Function
open import Structure.Operator
open import Syntax.Function

record Summation ⦃ monoid : Monoid(_▫_) ⦄ {ℓᵢ} : Type{Lvl.𝐒(ℓᵢ) Lvl.⊔ ℓᵣ Lvl.⊔ ℓ Lvl.⊔ ℓₑ} where
  field
    Index : Range → Type{ℓᵢ}
    ∑ : (r : Range) → (Index(r) → T) → T

  open Monoid(monoid)
  field
    preserves-operator : ∀{r}{f g} → (∑(r) (x ↦ f(x) ▫ g(x)) ≡ (∑(r) f) ▫ (∑(r) g))
    preserves-identity : ∀{r} → (∑(r) (_ ↦ id) ≡ id)
open Summation ⦃ … ⦄
