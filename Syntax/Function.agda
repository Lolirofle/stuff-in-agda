module Syntax.Function where

import Lvl

infix 2 [↦] [↦ₜ] [↦ᵢₘ] [⤇]

-- Custom syntax for an anonymous function
[↦] : ∀{ℓ}{T : Set(ℓ)} → T → T
[↦] x = x
syntax [↦](λ x → y) = x ↦ y
{-# DISPLAY [↦] x = x #-}

-- Custom syntax for an anonymous function with a type annotation
[↦ₜ] : ∀{ℓ₁ ℓ₂}{A : Set(ℓ₁)}{B : Set(ℓ₂)} → (A → B) → (A → B)
[↦ₜ] x = x
syntax [↦ₜ]{B = t}(λ x → y) = x :of: t ↦ y
{-# DISPLAY [↦ₜ] x = x #-}

-- Custom syntax for an anonymous function with an implicit argument
[↦ᵢₘ] : ∀{ℓ₁ ℓ₂}{A : Set(ℓ₁)}{B : Set(ℓ₂)} → (A → B) → ({_ : A} → B)
[↦ᵢₘ] f{x} = f(x)
syntax [↦ᵢₘ](λ x → y) = x ↦ᵢₘ y
{-# DISPLAY [↦ᵢₘ] x = x #-}

-- Custom syntax for an anonymous function with an instance argument
[⤇] : ∀{ℓ₁ ℓ₂}{A : Set(ℓ₁)}{B : Set(ℓ₂)} → (A → B) → (⦃ _ : A ⦄ → B)
[⤇] f ⦃ x ⦄ = f(x)
syntax [⤇](λ x → y) = x ⤇ y
{-# DISPLAY [⤇] x = x #-}
