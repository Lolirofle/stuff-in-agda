module Structure.Function.Linear{ℓ₁}{ℓ₂} where

import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Relator.Equals.Proofs{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

record LinearMap {V₁ V₂ S : Type} (_+₁_ : V₁ → V₁ → V₁) (_⋅₁_ : S → V₁ → V₁)  (_+₂_ : V₂ → V₂ → V₂) (_⋅₂_ : S → V₂ → V₂) (f : V₁ → V₂) : Stmt where
  field
    additivity   : ∀{v₁ v₂ : V₁} → (f(v₁ +₁ v₂) ≡ f(v₁) +₂ f(v₂))
    homogeneity1 : ∀{s : S} → ∀{v : V₁} → (f(s ⋅₁ v) ≡ s ⋅₂ f(v))
