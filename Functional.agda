module Functional where

import      Lvl
open import Type

infixl 10000 _∘_
infixl 10000 _⩺_
infixl 10000 _⩹_
infixl 30 _→ᶠ_ _←_ _←ᶠ_
infixr 0 _$_

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T X X₁ X₂ X₃ Y Y₁ Y₂ Y₃ Z : Type{ℓ}

-- Converse of a function type
_←_ : Type{ℓ₁} → Type{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}
Y ← X = X → Y

-- Function type as a function
_→ᶠ_ : Type{ℓ₁} → Type{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}
X →ᶠ Y = X → Y

-- Converse function type as a function
_←ᶠ_ : Type{ℓ₁} → Type{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}
Y ←ᶠ X = Y ← X



-- The identity function.
-- Returns the applied argument.
id : T → T
id(x) = x

-- The constant function.
-- Returns the first argument independent of the second.
const : let _ = X in Y → (X → Y)
const(x)(_) = x

-- Function application as a function.
-- Applies the first argument on the function on the second argument.
apply : let _ = X in X → (X → Y) → Y
apply(x)(f) = f(x)

-- Function application as an operator
_$_ : (X → Y) → X → Y
_$_ = id

-- Function application as an operator. Function to the left, value to the right.
_⩹_ : (X → Y) → X → Y
f ⩹ x = f(x)
-- Function application as an operator. Value to the left, function to the right.
_⩺_ : X → (X → Y) → Y
x ⩺ f = f(x)

-- Swapping the arguments of a binary operation
swap : (X → Y → Z) → (Y → X → Z)
swap f(y)(x) = f(x)(y)

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

-- TODO: Move these to Function.Multi
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

-- map₂Arg₁ : let _ = X in (Y₁ → Y₂ → Z) → (X → Y₁) → (X → Y₂) → (X → Z)
-- map₂Arg₁ f g₁ g₂ x = f(g₁ x)(g₂ x)

-- map₂Arg₂ : let _ = X₁ ; _ = X₂ in (Y₁ → Y₂ → Z) → (X₁ → Y₁) → (X₂ → Y₂) → (X₁ → X₂ → Z)
-- map₂Arg₂ f g₁ g₂ x₁ x₂ = f(g₁ x₁)(g₂ x₂)

-- Function lifting //TODO: Consider removing because it is the same as _∘_
liftₗ : (X → Y) → ((Z → X) → (Z → Y))
liftₗ = _∘_ -- liftₗ(f) = f ∘_

liftᵣ : (X → Y) → ((Y → Z) → (X → Z))
liftᵣ = swap(_∘_) -- liftᵣ(f) = _∘ f

open import Syntax.Function public
