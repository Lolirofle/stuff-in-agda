module Structure.Function.Linear lvl where

open import Logic(lvl)
open import Relator.Equals(lvl)

record LinearMap {V S : Set} (f : V → V) (_+_ : V → V → V) (_⋅_ : S → V → V) : Stmt where
  field
    additivity   : ∀{v₁ v₂ : V} → (f(v₁ + v₂) ≡ f(v₁) + f(v₂))
    homogeneity1 : ∀{s : S} → ∀{v : V} → (f(s ⋅ v) ≡ s ⋅ f(v))
