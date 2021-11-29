module Functional.Irrelevant where

import      Lvl
open import Type

infixl 10000 _∘ᵢᵣᵣ_ _∘ᵢᵣᵣ₁_ _∘ᵢᵣᵣ₂_ _∘ᵢᵣᵣ₁₂_
infixl 30 _→ᵢᵣᵣ_ _←ᵢᵣᵣ_
infixr 0 _$ᵢᵣᵣ_

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T X X₁ X₂ X₃ X₄ Y Y₁ Y₂ Y₃ Y₄ Z : Type{ℓ}

-- Instance function type.
_→ᵢᵣᵣ_ : Type{ℓ₁} → Type{ℓ₂} → Type
X →ᵢᵣᵣ Y = .X → Y
{-# INLINE _→ᵢᵣᵣ_ #-}

-- Converse of an instance function type.
_←ᵢᵣᵣ_ : Type{ℓ₁} → Type{ℓ₂} → Type
Y ←ᵢᵣᵣ X = X →ᵢᵣᵣ Y
{-# INLINE _←ᵢᵣᵣ_ #-}

_$ᵢᵣᵣ_ : (X →ᵢᵣᵣ Y) → (X → Y)
f $ᵢᵣᵣ x = f(x)
{-# INLINE _$ᵢᵣᵣ_ #-}

_∘ᵢᵣᵣ₂_ : (Y → Z) → (X →ᵢᵣᵣ Y) → (X →ᵢᵣᵣ Z)
(f ∘ᵢᵣᵣ₂ g)(x) = f(g(x))
{-# INLINE _∘ᵢᵣᵣ₂_ #-}

_∘ᵢᵣᵣ₁₂_ : (Y →ᵢᵣᵣ Z) → (X → Y) →ᵢᵣᵣ (X →ᵢᵣᵣ Z)
(f ∘ᵢᵣᵣ₁₂ g)(x) = f(g(x))
{-# INLINE _∘ᵢᵣᵣ₁₂_ #-}

_∘ᵢᵣᵣ₁_ : (Y →ᵢᵣᵣ Z) → (X → Y) → (X →ᵢᵣᵣ Z)
f ∘ᵢᵣᵣ₁ g = (f ∘ᵢᵣᵣ₁₂_) $ᵢᵣᵣ g
{-# INLINE _∘ᵢᵣᵣ₁_ #-}

_∘ᵢᵣᵣ_ : (Y →ᵢᵣᵣ Z) → (X →ᵢᵣᵣ Y) → (X →ᵢᵣᵣ Z)
f ∘ᵢᵣᵣ g = f ∘ᵢᵣᵣ₁₂ (g $ᵢᵣᵣ_)
{-# INLINE _∘ᵢᵣᵣ_ #-}

constᵢᵣᵣ : Y → (.X → Y)
constᵢᵣᵣ y _ = y
{-# INLINE constᵢᵣᵣ #-}
