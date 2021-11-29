open import Structure.Operator.Monoid
open import Structure.Setoid
open import Type

module Operator.Summation3 {ℓᵣ ℓᵢ ℓ ℓₑ} {T : Type{ℓ}} (Index : Type{ℓᵢ}) (Range : (Index → T) → Type{ℓᵣ}) (_▫_ : T → T → T) ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where

{-
open import Functional using (pointwise₂,₁ ; const)
import      Lvl
open import Structure.Function
open import Structure.Operator
open import Syntax.Function

record Summation ⦃ monoid : Monoid(_▫_) ⦄ : Type{Lvl.𝐒(ℓᵢ) Lvl.⊔ ℓᵣ Lvl.⊔ ℓ Lvl.⊔ ℓₑ} where
  field
    ∑ : (f : Index → T) → Range(f) → T

  open Monoid(monoid)
  field
    range-operator : 
  field
    preserves-operator : ∀{f g}{r} → (∑(pointwise₂,₁(_▫_) f g)(r) ≡ (∑ f(r)) ▫ (∑ g(r)))
    preserves-identity : ∀{r} → (∑(const id)(r) ≡ id)
open Summation ⦃ … ⦄
-}
