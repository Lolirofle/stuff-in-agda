module Structure.Function.Linear {ℓ₁} {ℓ₂} where

import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

record LinearMap {V S : Type} (f : V → V) (_+_ : V → V → V) (_⋅_ : S → V → V) : Stmt where
  field
    additivity   : ∀{v₁ v₂ : V} → (f(v₁ + v₂) ≡ f(v₁) + f(v₂))
    homogeneity1 : ∀{s : S} → ∀{v : V} → (f(s ⋅ v) ≡ s ⋅ f(v))
