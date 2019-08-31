open import Type

module Relator.Congruence {ℓ₁}{ℓ₂} {X : Type{ℓ₁}}{Y : Type{ℓ₂}} where

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Relator.Equals

infixl 15 _≅_of_
data _≅_of_ (x₁ : X) (x₂ : X) (f : X → Y) : Stmt{ℓ₂} where
  instance [≅]-intro : (f(x₁) ≡ f(x₂)) → (x₁ ≅ x₂ of f)

[≅]-elim : ∀{x₁ x₂ : X}{f : X → Y} → (x₁ ≅ x₂ of f) → (f(x₁) ≡ f(x₂))
[≅]-elim ([≅]-intro eq) = eq
