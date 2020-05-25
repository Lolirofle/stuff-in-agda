module Syntax.Function where

import      Lvl
open import Type
open import Syntax.Type

infix 2 [↦] [⤠] [⤇]

-- Custom syntax for an anonymous function
[↦] : ∀{ℓ}{T : Type{ℓ}} → T → T
[↦] x = x
syntax [↦](λ x → y) = x ↦ y
{-# DISPLAY [↦] x = x #-}

-- Custom syntax for an anonymous function with an implicit argument
[⤠] : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B) → ({_ : A} → B)
[⤠] f{x} = f(x)
syntax [⤠](λ x → y) = x ⤠ y
{-# DISPLAY [⤠] x = x #-}

-- Custom syntax for an anonymous function with an instance argument
[⤇] : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B) → (⦃ _ : A ⦄ → B)
[⤇] f ⦃ x ⦄ = f(x)
syntax [⤇](λ x → y) = x ⤇ y
{-# DISPLAY [⤇] x = x #-}

-- Functions with two parameters as an infix binary operator
_⦗_⦘_ : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}} → A → (A → B → C) → B → C
a ⦗ op ⦘ b = op a b

infixl 10000 _⦗_⦘_
infixl 10000 _⦗_⦘ₗ_
infixr 10000 _⦗_⦘ᵣ_

_⦗_⦘ₗ_ = _⦗_⦘_
_⦗_⦘ᵣ_ = _⦗_⦘_
