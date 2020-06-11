module Syntax.Function where

import      Lvl
open import Type
open import Syntax.Type

private variable ℓ : Lvl.Level
private variable T A B C : Type{ℓ}

infix 2 [↦] [⤠] [⤇]

-- Custom syntax for an anonymous function
-- Example:
--   f : A → A
--   f = a ↦ a
--
--   g : (A → A → A) → (A → A → A)
--   g(_▫_) = a₁ ↦ a₂ ↦ (a₁ ▫ a₂)
[↦] : T → T
[↦] x = x
syntax [↦](\x → y) = x ↦ y
{-# DISPLAY [↦] x = x #-}

-- Custom syntax for an anonymous function with an implicit argument
-- Example:
--   f : A → A
--   f = a ↦ a
[⤠] : (A → B) → ({A} → B)
[⤠] f{x} = f(x)
syntax [⤠](\x → y) = x ⤠ y
{-# DISPLAY [⤠] x = x #-}

-- Custom syntax for an anonymous function with an instance argument
[⤇] : (A → B) → (⦃ _ : A ⦄ → B)
[⤇] f ⦃ x ⦄ = f(x)
syntax [⤇](\x → y) = x ⤇ y
{-# DISPLAY [⤇] x = x #-}

-- Functions with two parameters as an infix binary operator
_⦗_⦘_ : A → (A → B → C) → B → C
a ⦗ op ⦘ b = op a b

infix  10000 _⦗_⦘_
infixl 10000 _⦗_⦘ₗ_
infixr 10000 _⦗_⦘ᵣ_

_⦗_⦘ₗ_ = _⦗_⦘_
_⦗_⦘ᵣ_ = _⦗_⦘_

{- TODO: Fix these with stuff in Lang.Function
f : {a : A} → A
f = (a ⤠ a)

g : ⦃ a₁ : A ⦄ ⦃ a₂ : A ⦄ → A
g = (a₁ ⤇ a₂ ⤇ a₁)
-}
