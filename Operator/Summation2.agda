open import Structure.Operator.Monoid
open import Structure.Setoid
open import Type

module Operator.Summation2 {ℓᵣ ℓ ℓₑ} (Range : Type{ℓᵣ}) {T : Type{ℓ}} (_▫_ : T → T → T) ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where

open import Functional using (pointwise₂,₁ ; const)
import      Lvl
open import Structure.Function
open import Structure.Operator
open import Syntax.Function

record Summation ⦃ monoid : Monoid(_▫_) ⦄ {ℓᵢ ℓₚ} : Type{Lvl.𝐒(ℓᵢ) Lvl.⊔ Lvl.𝐒(ℓₚ) Lvl.⊔ ℓᵣ Lvl.⊔ ℓ Lvl.⊔ ℓₑ} where
  field
    Index : Range → Type{ℓᵢ}
    Summable : (r : Range) → (Index(r) → T) → Type{ℓₚ}
    ∑ : (r : Range) → (f : Index(r) → T) → ⦃ summable : Summable r f ⦄ → T

  open Monoid(monoid)
  field
    summable-operator : ∀{r}{f g} ⦃ sf : Summable r f ⦄ ⦃ sg : Summable r g ⦄ → Summable r (pointwise₂,₁(_▫_) f g)
    summable-identity : ∀{r} → Summable r (const id)
  field
    preserves-operator : ∀{r}{f g} ⦃ sf ⦄ ⦃ sg ⦄ → (∑(r) (pointwise₂,₁(_▫_) f g) ⦃ summable-operator ⦄ ≡ (∑(r) f ⦃ sf ⦄) ▫ (∑(r) g ⦃ sg ⦄))
    preserves-identity : ∀{r} → (∑(r) (const id) ⦃ summable-identity ⦄ ≡ id)
open Summation ⦃ … ⦄
