module Functional.Irrelevant where

import      Lvl
open import Type

infixl 10000 _∘ᵢᵣᵣ_ _∘ᵢᵣᵣ₀_ _∘ᵢᵣᵣ₋_
infixl 30 _→ᵢᵣᵣ_ _←ᵢᵣᵣ_
infixr 0 _$ᵢᵣᵣ_

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T X X₁ X₂ X₃ X₄ Y Y₁ Y₂ Y₃ Y₄ Z : Type{ℓ}

-- Instance function type.
_→ᵢᵣᵣ_ : Type{ℓ₁} → Type{ℓ₂} → Type
X →ᵢᵣᵣ Y = ⦃ X ⦄ → Y
{-# INLINE _→ᵢᵣᵣ_ #-}

-- Converse of an instance function type.
_←ᵢᵣᵣ_ : Type{ℓ₁} → Type{ℓ₂} → Type
Y ←ᵢᵣᵣ X = X →ᵢᵣᵣ Y
{-# INLINE _←ᵢᵣᵣ_ #-}

_$ᵢᵣᵣ_ : (.X → Y) → (X → Y)
f $ᵢᵣᵣ x = f(x)
{-# INLINE _$ᵢᵣᵣ_ #-}

_∘ᵢᵣᵣ₀_ : (Y → Z) → (.X → Y) → (.X → Z)
(f ∘ᵢᵣᵣ₀ g)(x) = f(g(x))
{-# INLINE _∘ᵢᵣᵣ₀_ #-}

_∘ᵢᵣᵣ₋_ : (.Y → Z) → .(X → Y) → (.X → Z)
(f ∘ᵢᵣᵣ₋ g)(x) = f(g(x))
{-# INLINE _∘ᵢᵣᵣ₋_ #-}

_∘ᵢᵣᵣ_ : (.Y → Z) → (.X → Y) → (.X → Z)
f ∘ᵢᵣᵣ g = f ∘ᵢᵣᵣ₋ (g $ᵢᵣᵣ_)
{-# INLINE _∘ᵢᵣᵣ_ #-}

constᵢᵣᵣ : Y → (.X → Y)
constᵢᵣᵣ y _ = y
{-# INLINE constᵢᵣᵣ #-}
