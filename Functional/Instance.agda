module Functional.Instance where

import      Lvl
open import Type

infixl 10000 _⦃∘⦄_
infixl 30 _⦃→⦄_ _⦃←⦄_
infixr 0 _⦃$⦄_

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T X X₁ X₂ X₃ X₄ Y Y₁ Y₂ Y₃ Y₄ Z : Type{ℓ}

-- Instance function type.
_⦃→⦄_ : Type{ℓ₁} → Type{ℓ₂} → Type
X ⦃→⦄ Y = ⦃ X ⦄ → Y
{-# INLINE _⦃→⦄_ #-}

-- Converse of an instance function type.
_⦃←⦄_ : Type{ℓ₁} → Type{ℓ₂} → Type
Y ⦃←⦄ X = X ⦃→⦄ Y
{-# INLINE _⦃←⦄_ #-}

_⦃$⦄_ : (⦃ _ : X ⦄ → Y) → (X → Y)
f ⦃$⦄ x = f ⦃ x ⦄
{-# INLINE _⦃$⦄_ #-}

-- Function composition on instance arguments.
_⦃∘⦄_ : let _ = X in (⦃ Y ⦄ → Z) → (⦃ X ⦄ → Y) → (⦃ X ⦄ → Z)
(f ⦃∘⦄ g) ⦃ x ⦄ = f ⦃ g ⦃ x ⦄ ⦄
{-# INLINE _⦃∘⦄_ #-}
