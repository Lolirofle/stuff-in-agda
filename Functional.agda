module Functional where

import      Lvl
open import Type

infixl 10000 _∘_

-- Function type as a function
_→ᶠ_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}
x →ᶠ y = x → y

-- Converse of a function type
_←_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}
y ← x = x → y

-- Identity functions
id : ∀{ℓ} → {T : Type{ℓ}} → T → T
id(x) = x

-- Constant functions
const : ∀{ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → T₁ → (T₂ → T₁)
const(x)(_) = x

-- Function application as a function
apply : ∀{ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → T₁ → (T₁ → T₂) → T₂
apply(x)(f) = f(x)

-- Function composition
_∘_ : ∀{ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (Y → Z) → (X → Y) → (X → Z)
(f ∘ g)(x) = f(g(x))

_∘₂_ : ∀{ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X₁ : Type{ℓ₁}}{X₂ : Type{ℓ₂}}{Y : Type{ℓ₃}}{Z : Type{ℓ₄}} → (Y → Z) → (X₁ → X₂ → Y) → (X₁ → X₂ → Z)
(f ∘₂ g)(x₁)(x₂) = f(g(x₁)(x₂))

_∘₃_ : ∀{ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {X₁ : Type{ℓ₁}}{X₂ : Type{ℓ₂}}{X₃ : Type{ℓ₃}}{Y : Type{ℓ₄}}{Z : Type{ℓ₅}} → (Y → Z) → (X₁ → X₂ → X₃ → Y) → (X₁ → X₂ → X₃ → Z)
(f ∘₃ g)(x)(y)(z) = f(g(x)(y)(z))

-- Function lifting //TODO: Consider removing because it is the same as _∘_
liftₗ : ∀{ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (X → Y) → ((Z → X) → (Z → Y))
liftₗ f g = f ∘ g

liftᵣ : ∀{ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (X → Y) → ((Y → Z) → (X → Z))
liftᵣ f g = g ∘ f

-- Swapping the arguments of a binary operation
swap : ∀{ℓ₁ ℓ₂ ℓ₃} {T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}}{T₃ : Type{ℓ₃}} → (T₁ → T₂ → T₃) → (T₂ → T₁ → T₃)
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
⊷_ : ∀{ℓ₁ ℓ₂} {A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B) → Type{ℓ₁}
⊷_ {_}{_} {A}{_} _ = A

-- Returns the codomain/image of a function
⊶_ : ∀{ℓ₁ ℓ₂} {A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B) → Type{ℓ₂}
⊶_ {_}{_} {_}{B} _ = B

-- Returns a function with a smaller domain
restrict : ∀{ℓ₁ ℓ₂ ℓ₃} {A₁ : Type{ℓ₁}}{A₂ : Type{ℓ₂}}{B : Type{ℓ₃}} {_ : A₂ → A₁} → (A₁ → B) → (A₂ → B)
restrict {_}{_}{_} {_}{_}{_} {tf} f = f ∘ tf

-- Returns a function with a larger codomain
expand : ∀{ℓ₁ ℓ₂ ℓ₃} {A : Type{ℓ₁}}{B₁ : Type{ℓ₂}}{B₂ : Type{ℓ₃}} {_ : B₁ → B₂} → (A → B₁) → (A → B₂)
expand {_}{_}{_} {_}{_}{_} {tf} f = tf ∘ f

-- Functions with two paramters as an infix binary operator
_〔_〕_ : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}} → A → (A → B → C) → B → C
a 〔 op 〕 b = op a b

-- Infers/resolves/(searches for) an instance/proof of the specified type/statement
resolve-instance : ∀{ℓ}(T : Type{ℓ}) {{_ : T}} → T
resolve-instance (_) {{x}} = x

-- Infers/resolves/(searches for) an instance/proof of an inferred type/statement
infer : ∀{ℓ}{T : Type{ℓ}} {{_ : T}} → T
infer {{x}} = x
