module Syntax.Method where

open import Type

{- TODO: Does not work. Needs to have higher precedence than function application
-- Function application in reversed order
_::_ : ∀{ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → T₁ → (T₁ → T₂) → T₂
x :: f = f(x)
infixl 1 _::_

import      Lvl
open import Relator.Equals{Lvl.𝟎}{Lvl.𝟎}

test : ∀{A X Y Z W : Type{Lvl.𝟎}}{a x y}{f : A → X → Y}{g : Y → Z → W} → (g(f(a)(x))(y) ≡ (a :: f(x) :: g)(y))
test = [≡]-intro
-}
