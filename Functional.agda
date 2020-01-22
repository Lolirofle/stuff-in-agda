module Functional where

import      Lvl
open import Type

infixl 10000 _∘_
infixl 10000 _⩺_
infixl 10000 _⩹_
infixl 30 _→ᶠ_ _←_ _←ᶠ_

-- Converse of a function type
_←_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}
y ← x = x → y

-- Function type as a function
_→ᶠ_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}
x →ᶠ y = x → y

-- Converse function type as a function
_←ᶠ_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}
y ←ᶠ x = y ← x



-- The identity function.
-- Returns the applied argument.
id : ∀{ℓ} {T : Type{ℓ}} → T → T
id(x) = x

-- The constant function.
-- Returns the first argument independent of the second.
const : ∀{ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → T₂ → (T₁ → T₂)
const(x)(_) = x

-- Function application as a function.
-- Applies the first argument on the function on the second argument.
apply : ∀{ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → T₁ → (T₁ → T₂) → T₂
apply(x)(f) = f(x)

-- Function application as an operator
_$_ : ∀{ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ → T₂) → T₁ → T₂
_$_ = id

-- Function application as an operator. Function to the left, value to the right.
_⩹_ : ∀{ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ → T₂) → T₁ → T₂
f ⩹ x = f(x)
-- Function application as an operator. Value to the left, function to the right.
_⩺_ : ∀{ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → T₁ → (T₁ → T₂) → T₂
x ⩺ f = f(x)

-- Swapping the arguments of a binary operation
swap : ∀{ℓ₁ ℓ₂ ℓ₃} {T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}}{T₃ : Type{ℓ₃}} → (T₁ → T₂ → T₃) → (T₂ → T₁ → T₃)
swap f(x₂)(x₁) = f(x₁)(x₂)

-- Function composition
_∘_ : ∀{ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (Y → Z) → (X → Y) → (X → Z)
(f ∘ g)(x) = f(g(x))

-- Function composition on implicit argument
_∘ᵢₘₚₗ_ : ∀{ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (Y → Z) → ({X} → Y) → ({X} → Z)
(f ∘ᵢₘₚₗ g){x} = f(g{x})

-- Function composition on instance argument
_∘ᵢₙₛₜ_ : ∀{ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (Y → Z) → (⦃ X ⦄ → Y) → (⦃ X ⦄ → Z)
(f ∘ᵢₙₛₜ g) ⦃ x ⦄ = f(g ⦃ x ⦄)

-- Function composition on a binary operator
-- A function is composed on every argument of the binary operator.
_on₂_ : ∀{ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (Y → Y → Z) → (X → Y) → (X → X → Z)
((_▫_) on₂ f)(y₁)(y₂) = f(y₁) ▫ f(y₂)

-- The S-combinator from combinatory logic.
-- It is sometimes described as a generalized version of the application operator or the composition operator.
-- Note: TODO: Applicative instance
s-combinator : ∀{ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (X → Y → Z) → (X → Y) → (X → Z)
s-combinator f g x = (f x) (g x)

-- TODO: Move these to Function.Multi
_∘₀_ : ∀{ℓ₁ ℓ₂} {Y : Type{ℓ₁}}{Z : Type{ℓ₂}} → (Y → Z) → Y → Z
_∘₀_ = id

_∘₁_ : ∀{ℓ₁ ℓ₂ ℓ₃} {X₁ : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (Y → Z) → (X₁ → Y) → (X₁ → Z)
_∘₁_ f = (f ∘₀_) ∘_

-- (f ∘₂ g)(x)(y) = f(g(x)(y))
_∘₂_ : ∀{ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X₁ : Type{ℓ₁}}{X₂ : Type{ℓ₂}}{Y : Type{ℓ₃}}{Z : Type{ℓ₄}} → (Y → Z) → (X₁ → X₂ → Y) → (X₁ → X₂ → Z)
_∘₂_ f = (f ∘₁_) ∘_

-- (f ∘₃ g)(x)(y)(z) = f(g(x)(y)(z))
_∘₃_ : ∀{ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {X₁ : Type{ℓ₁}}{X₂ : Type{ℓ₂}}{X₃ : Type{ℓ₃}}{Y : Type{ℓ₄}}{Z : Type{ℓ₅}} → (Y → Z) → (X₁ → X₂ → X₃ → Y) → (X₁ → X₂ → X₃ → Z)
_∘₃_ f = (f ∘₂_) ∘_

-- Function lifting //TODO: Consider removing because it is the same as _∘_
liftₗ : ∀{ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (X → Y) → ((Z → X) → (Z → Y))
liftₗ = _∘_ -- liftₗ(f) = f ∘_

liftᵣ : ∀{ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (X → Y) → ((Y → Z) → (X → Z))
liftᵣ = swap(_∘_) -- liftᵣ(f) = _∘ f

open import Syntax.Function public
