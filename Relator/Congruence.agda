module Relator.Congruence {ℓ₁} {ℓ₂} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

infixl 15 _≅_of_
data _≅_of_ {X Y : Type} (x₁ : X) (x₂ : X) (f : X → Y) : Stmt where
  instance [≅]-intro : (f(x₁) ≡ f(x₂)) → (x₁ ≅ x₂ of f)

[≅]-elim : ∀{X Y} → ∀{x₁ x₂ : X}{f : X → Y} → (x₁ ≅ x₂ of f) → (f(x₁) ≡ f(x₂))
[≅]-elim ([≅]-intro eq) = eq
