module Function.Equals.Multi where

open import Data.Tuple.Raise
open import Data.Tuple.RaiseTypeᵣ
open import Functional
open import Function.Multi.Functions
open import Function.Multi
open import Logic
open import Logic.Predicate
open import Logic.Predicate.Multi
import      Lvl
import      Lvl.MultiFunctions as Lvl
open import Numeral.Natural
open import Structure.Setoid
open import Syntax.Function
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable n : ℕ
private variable ℓ𝓈 : Lvl.Level ^ n

module Names where
  -- Pointwise function equality for a pair of multivariate functions.
  -- Example:
  --   (f ⦗ ⊜₊(3) ⦘ g) = (∀{x}{y}{z} → (f(x)(y)(z) ≡ g(x)(y)(z)))
  ⊜₊ : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)}{B : Type{ℓ}} ⦃ equiv-B : Equiv{ℓₑ}(B) ⦄ → (As ⇉ B) → (As ⇉ B) → Stmt{ℓₑ Lvl.⊔ (Lvl.⨆(ℓ𝓈))}
  ⊜₊(n) = ∀₊(n) ∘₂ pointwise(n)(2) (_≡_)

record ⊜₊ (n : ℕ) {ℓ𝓈}{As : Types{n}(ℓ𝓈)}{B : Type{ℓ}} ⦃ equiv-B : Equiv{ℓₑ}(B) ⦄ (f : As ⇉ B) (g : As ⇉ B) : Stmt{ℓₑ Lvl.⊔ (Lvl.⨆(ℓ𝓈))} where
  constructor intro
  field proof : f ⦗ Names.⊜₊(n) ⦘ g
