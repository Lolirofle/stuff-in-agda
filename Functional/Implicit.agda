module Functional.Implicit where

open import Lang.Function
import      Lvl
open import Type

infixl 10000 _﹛∘﹜_
infixl 30 _﹛→﹜_ _﹛←﹜_
infixr 0 _﹛$﹜_

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T X X₁ X₂ X₃ X₄ Y Y₁ Y₂ Y₃ Y₄ Z : Type{ℓ}

-- Implicit function type.
_﹛→﹜_ : Type{ℓ₁} → Type{ℓ₂} → Type
X ﹛→﹜ Y = {X} → Y
{-# INLINE _﹛→﹜_ #-}

-- Converse of an implicit function type.
_﹛←﹜_ : Type{ℓ₁} → Type{ℓ₂} → Type
Y ﹛←﹜ X = X ﹛→﹜ Y
{-# INLINE _﹛←﹜_ #-}

﹛id﹜ : {@(tactic no-infer) x : X} → X
﹛id﹜{x = x} = x
{-# INLINE ﹛id﹜ #-}

_﹛$﹜_ : ({@(tactic no-infer) x : X} → Y) → (X → Y)
f ﹛$﹜ x = f{x}
{-# INLINE _﹛$﹜_ #-}

-- Function composition on implicit argument
_﹛∘﹜_ : let _ = X in ({@(tactic no-infer) y : Y} → Z) → ({@(tactic no-infer) x : X} → Y) → ({@(tactic no-infer) x : X} → Z)
(f ﹛∘﹜ g){x} = f{g{x}}
{-# INLINE _﹛∘﹜_ #-}
