module Structure.Function.Linear where

import      Lvl
open import Logic
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs
open import Type

-- TODO: Remove this
module _ {ℓ₁}{ℓ₂}{ℓ₃} {V₁ : Type{ℓ₁}} {V₂ : Type{ℓ₂}} {S : Type{ℓ₃}} where
  record LinearMap  (_+₁_ : V₁ → V₁ → V₁) (_⋅₁_ : S → V₁ → V₁)  (_+₂_ : V₂ → V₂ → V₂) (_⋅₂_ : S → V₂ → V₂) (f : V₁ → V₂) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    field
      additivity   : ∀{v₁ v₂ : V₁} → (f(v₁ +₁ v₂) ≡ f(v₁) +₂ f(v₂))
      homogeneity1 : ∀{s : S} → ∀{v : V₁} → (f(s ⋅₁ v) ≡ s ⋅₂ f(v))
