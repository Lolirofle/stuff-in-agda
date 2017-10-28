module Relator.FunctionEquals {ℓ₁} {ℓ₂} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
import      Relator.Equals{ℓ₁}{ℓ₂} as Equals
open import Structure.Relator.Equivalence{ℓ₁}{ℓ₂}
open import Structure.Relator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

private _≡ᵢ_ = Equals._≡_

infixl 15 _≡_
_≡_ : ∀{T₁ T₂ : Type} → (T₁ → T₂) → (T₁ → T₂) → Stmt
_≡_ f₁ f₂ = (∀{x} → (f₁(x) ≡ᵢ f₂(x)))

_≢_ : ∀{T₁ T₂ : Type} → (T₁ → T₂) → (T₁ → T₂) → Stmt
_≢_ a b = ¬(a ≡ b)
