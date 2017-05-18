module Functional where

import      Level as Lvl
open import Type

infixl 10000 _∘_

-- Function type as a function
_→ᶠ_ : ∀{l₁ l₂} → Type{l₁} → Type{l₂} → Type{l₁ Lvl.⊔ l₂}
x →ᶠ y = x → y

-- Converse of a function type
_←_ : ∀{l₁ l₂} → Type{l₁} → Type{l₂} → Type{l₁ Lvl.⊔ l₂}
y ← x = x → y

-- Identity functions
id : ∀{l} → {T : Type{l}} → T → T
id(x) = x

-- Constant functions
const : ∀{l₁ l₂} {T₁ : Type{l₁}}{T₂ : Type{l₂}} → T₁ → (T₂ → T₁)
const(x)(_) = x

-- Function application as a function
apply : ∀{l₁ l₂} {T₁ : Type{l₁}}{T₂ : Type{l₂}} → T₁ → (T₁ → T₂) → T₂
apply(x)(f) = f(x)

-- Function composition
_∘_ : ∀{l₁ l₂ l₃} {X : Type{l₁}}{Y : Type{l₂}}{Z : Type{l₃}} → (Y → Z) → (X → Y) → (X → Z)
(f ∘ g)(x) = f(g(x))

-- Function lifting //TODO: Consider removing because it is the same as _∘_
lift : ∀{l₁ l₂ l₃} {X : Type{l₁}}{Y : Type{l₂}}{Z : Type{l₃}} → (X → Y) → ((Z → X) → (Z → Y))
lift f g = f ∘ g

-- Swapping the arguments of a binary operation
swap : ∀{l₁ l₂ l₃} {T₁ : Type{l₁}}{T₂ : Type{l₂}}{T₃ : Type{l₃}} → (T₁ → T₂ → T₃) → (T₂ → T₁ → T₃)
swap(f)(x₂)(x₁) = f(x₁)(x₂)

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

-- Custom syntax for anonymous functions/mappings
syntax id(λ x → y) = x ↦ y

-- Returns the domain of a function
⊷_ : ∀{l₁ l₂} {A : Type{l₁}}{B : Type{l₂}} → (A → B) → Type{l₁}
⊷_ {_}{_} {A}{_} _ = A

-- Returns the codomain/image of a function
⊶_ : ∀{l₁ l₂} {A : Type{l₁}}{B : Type{l₂}} → (A → B) → Type{l₂}
⊶_ {_}{_} {_}{B} _ = B

-- Returns a function with a smaller domain
restrict : ∀{l₁ l₂ l₃} {A₁ : Type{l₁}}{A₂ : Type{l₂}}{B : Type{l₃}} {_ : A₂ → A₁} → (A₁ → B) → (A₂ → B)
restrict {_}{_}{_} {_}{_}{_} {tf} f = f ∘ tf

-- Returns a function with a larger codomain
expand : ∀{l₁ l₂ l₃} {A : Type{l₁}}{B₁ : Type{l₂}}{B₂ : Type{l₃}} {_ : B₁ → B₂} → (A → B₁) → (A → B₂)
expand {_}{_}{_} {_}{_}{_} {tf} f = tf ∘ f
