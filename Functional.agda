module Functional where

import      Lvl
open import Type

infixl 10000 _∘_
infixr 0 _$_
infixl 0 _₴_

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable A B C D E F T X X₁ X₂ X₃ X₄ Y Y₁ Y₂ Y₃ Y₄ Z : Type{ℓ}

open import Function using (_←_ ; _→ᶠ_ ; _←ᶠ_ ; id ; const) public

-- Swapping the arguments of a binary operation
swap : (X → Y → Z) → (Y → X → Z)
swap f(y)(x) = f(x)(y)
{-# INLINE swap #-}

-- Function application as an operator. The function on LHS, the value on RHS.
_$_ : (X → Y) → X → Y
_$_ = id
{-# INLINE _$_ #-}

-- Function application as an operator. The value on LHS, the function on RHS.
_₴_ : X → (X → Y) → Y
_₴_ = swap id
{-# INLINE _₴_ #-}
apply = _₴_
{-# INLINE apply #-}

-- Function composition
_∘_ : let _ = X in (Y → Z) → (X → Y) → (X → Z)
(f ∘ g)(x) = f(g(x))

-- Function composition on implicit argument
_∘ᵢₘₚₗ_ : let _ = X in ({Y} → Z) → ({X} → Y) → ({X} → Z)
(f ∘ᵢₘₚₗ g){x} = f{g{x}}

-- Function composition on instance argument
_∘ᵢₙₛₜ_ : let _ = X in (⦃ Y ⦄ → Z) → (⦃ X ⦄ → Y) → (⦃ X ⦄ → Z)
(f ∘ᵢₙₛₜ g) ⦃ x ⦄ = f ⦃ g ⦃ x ⦄ ⦄

-- The S-combinator from combinatory logic.
-- It is sometimes described as a generalized version of the application operator or the composition operator.
-- Note: TODO: Applicative instance
_∘ₛ_ : (X → Y → Z) → (X → Y) → (X → Z)
(f ∘ₛ g)(x) = (f x) (g x)

_on₀_ : let _ = X in Z → (X → Y) → Z
((▫) on₀ f) = ▫ -- const

_on₁_ : let _ = X in (Y → Z) → (X → Y) → (X → Z)
((_▫) on₁ f)(y₁) = (f(y₁) ▫) on₀ f -- f(y₁) ▫

-- Function composition on a binary operator
-- A function is composed on every argument of the binary operator.
_on₂_ : let _ = X in (Y → Y → Z) → (X → Y) → (X → X → Z)
((_▫_) on₂ f)(y₁) = (f(y₁) ▫_) on₁ f -- f(y₁) ▫ f(y₂)

_on₃_ : let _ = X in (Y → Y → Y → Z) → (X → Y) → (X → X → X → Z)
((_▫_▫_) on₃ f)(y₁) = (f(y₁) ▫_▫_) on₂ f -- f(y₁) ▫ f(y₂) ▫ f(y₃)

_∘₀_ : (Y → Z) → Y → Z
_∘₀_ = id

_∘₁_ : let _ = X₁ in (Y → Z) → (X₁ → Y) → (X₁ → Z)
_∘₁_ f = (f ∘₀_) ∘_

-- (f ∘₂ g)(x)(y) = f(g(x)(y))
_∘₂_ : let _ = X₁ ; _ = X₂ in (Y → Z) → (X₁ → X₂ → Y) → (X₁ → X₂ → Z)
_∘₂_ f = (f ∘₁_) ∘_

-- (f ∘₃ g)(x)(y)(z) = f(g(x)(y)(z))
_∘₃_ : let _ = X₁ ; _ = X₂ ; _ = X₃ in (Y → Z) → (X₁ → X₂ → X₃ → Y) → (X₁ → X₂ → X₃ → Z)
_∘₃_ f = (f ∘₂_) ∘_

-- (f ∘₄ g)(x)(y)(z)(w) = f(g(x)(y)(z)(w))
_∘₄_ : let _ = X₁ ; _ = X₂ ; _ = X₃ ; _ = X₄ in (Y → Z) → (X₁ → X₂ → X₃ → X₄ → Y) → (X₁ → X₂ → X₃ → X₄ → Z)
_∘₄_ f = (f ∘₃_) ∘_

-- Function type lifting.
liftₗ : (X → Y) → ((Z → X) → (Z → Y))
liftₗ = _∘_

liftᵣ : (X → Y) → ((Y → Z) → (X → Z))
liftᵣ = swap(_∘_)

-- Applies an argument to two arguments of a binary function.
_$₂_ : (X → X → Y) → (X → Y)
f $₂ x = f x x

apply₂ : X → (X → X → Y) → Y
apply₂ = swap(_$₂_)

proj₂ₗ : X → Y → X
proj₂ₗ = const

proj₂ᵣ : X → Y → Y
proj₂ᵣ = const id

-- Alternative definition: pointwise₂,₁(_▫_) f g a = f(a) ▫ g(a)
pointwise₂,₁ : let _ = A in (B → C → D) → (A → B) → (A → C) → (A → D)
pointwise₂,₁(_▫_) = ((_∘ₛ_) ∘ ((_▫_) ∘_))
{-# INLINE pointwise₂,₁ #-}

-- Alternative definition: pointwise₂,₂(_▫_) f g a b = (f a b) ▫ (g a b)
pointwise₂,₂ : let _ = A ; _ = B in (C → D → E) → (A → B → C) → (A → B → D) → (A → B → E)
pointwise₂,₂(_▫_) = pointwise₂,₁(pointwise₂,₁(_▫_))
{-# INLINE pointwise₂,₂ #-}

-- Alternative definition: pointwise₂,₃(_▫_) f g a b c = (f a b c) ▫ (g a b c)
pointwise₂,₃ : let _ = A ; _ = B ; _ = C in (D → E → F) → (A → B → C → D) → (A → B → C → E) → (A → B → C → F)
pointwise₂,₃(_▫_) = pointwise₂,₁(pointwise₂,₂(_▫_))
{-# INLINE pointwise₂,₃ #-}

open import Syntax.Function public
