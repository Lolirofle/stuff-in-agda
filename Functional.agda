module Functional where

import      Lvl
open import Type

infixl 10000 _∘_

-- Converse of a function type
_←_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}
y ← x = x → y

-- Function type as a function
_→ᶠ_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}
x →ᶠ y = x → y

-- Converse function type as a function
_←ᶠ_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}
y ←ᶠ x = y ← x



-- Identity functions
id : ∀{ℓ} {T : Type{ℓ}} → T → T
id(x) = x

-- Constant functions
const : ∀{ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → T₁ → (T₂ → T₁)
const(x)(_) = x

-- Function application as a function
apply : ∀{ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → T₁ → (T₁ → T₂) → T₂
apply(x)(f) = f(x)

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

-- Swapped function composition on a binary operator
-- A function is composed on the arguments of the binary operator.
_on₂_ : ∀{ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (X → Y) → (Y → Y → Z) → (X → X → Z)
(f on₂ (_▫_))(y₁)(y₂) = f(y₁) ▫ f(y₂)



_∘₂_ : ∀{ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X₁ : Type{ℓ₁}}{X₂ : Type{ℓ₂}}{Y : Type{ℓ₃}}{Z : Type{ℓ₄}} → (Y → Z) → (X₁ → X₂ → Y) → (X₁ → X₂ → Z)
(f ∘₂ g)(x₁) = f ∘ (g(x₁))
-- (f ∘₂ g)(x₁)(x₂) = f(g(x₁)(x₂)) = curry(f ∘ (uncurry g))(x₁)(x₂) = (f ∘ (g(x₁)))(x₂)

_∘₃_ : ∀{ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {X₁ : Type{ℓ₁}}{X₂ : Type{ℓ₂}}{X₃ : Type{ℓ₃}}{Y : Type{ℓ₄}}{Z : Type{ℓ₅}} → (Y → Z) → (X₁ → X₂ → X₃ → Y) → (X₁ → X₂ → X₃ → Z)
(f ∘₃ g)(x₁) = f ∘₂ (g(x₁))
-- (f ∘₃ g)(x)(y)(z) = f(g(x)(y)(z))

-- Function lifting //TODO: Consider removing because it is the same as _∘_
liftₗ : ∀{ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (X → Y) → ((Z → X) → (Z → Y))
liftₗ = _∘_ -- liftₗ(f) = f ∘_

liftᵣ : ∀{ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (X → Y) → ((Y → Z) → (X → Z))
liftᵣ = swap _∘_ -- liftᵣ(f) = _∘ f



-- 🔁(f ∘ 2)
-- curry ∘ curry
-- (Y → Z) → ((X → Y) → (X → Z))
-- ((T₁ ⨯ T₂) → T₃) → (T₁ → (T₂ → T₃))
--   Y = ((T₁ ⨯ T₂) → T₃)
--   Z = (T₁ → (T₂ → T₃))
-- ((T₄ ⨯ T₅) → T₆) → (T₄ → (T₅ → T₆))
--   X = ((T₄ ⨯ T₅) → T₆)
--   Y = (T₄ → (T₅ → T₆))
-- 
--   T₄ = (T₁ ⨯ T₂)
--   (T₅ → T₆) = T₃

open import Syntax.Function public

-- Returns the domain type of a function
Domain : ∀{ℓ₁ ℓ₂} {A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B) → Type{ℓ₁}
Domain {_}{_} {A}{_} _ = A

-- Returns the codomain type of a function
Codomain : ∀{ℓ₁ ℓ₂} {A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B) → Type{ℓ₂}
Codomain {_}{_} {_}{B} _ = B

-- Functions with two parameters as an infix binary operator
_〔_〕_ : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}} → A → (A → B → C) → B → C
a 〔 op 〕 b = op a b

infixl 10000 _〔ₗ_〕_
infixr 10000 _〔ᵣ_〕_

_〔ₗ_〕_ = _〔_〕_
_〔ᵣ_〕_ = _〔_〕_
