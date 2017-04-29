module Functional where

infixl 10000 _∘_

-- Function type as a function
_→ᶠ_ : ∀{lvl} → Set(lvl) → Set(lvl) → Set(lvl)
x →ᶠ y = x → y

_←_ : ∀{lvl} → Set(lvl) → Set(lvl) → Set(lvl)
y ← x = x → y

id : ∀{lvl} → {T : Set(lvl)} → T → T
id(x) = x

const : ∀{n₁ n₂} {T₁ : Set n₁}{T₂ : Set n₂} → T₁ → (T₂ → T₁)
const(x)(_) = x

apply : ∀{n₁ n₂} {T₁ : Set n₁}{T₂ : Set n₂} → T₁ → (T₁ → T₂) → T₂
apply(x)(f) = f(x)

_∘_ : ∀{n₁ n₂ n₃} {X : Set n₁}{Y : Set n₂}{Z : Set n₃} → (Y → Z) → (X → Y) → (X → Z)
(f ∘ g)(x) = f(g(x))

lift : ∀{n₁ n₂ n₃} {X : Set n₁}{Y : Set n₂}{Z : Set n₃} → (X → Y) → ((Z → X) → (Z → Y))
lift f g = f ∘ g

swap : ∀{n₁ n₂ n₃} {T₁ : Set n₁}{T₂ : Set n₂}{T₃ : Set n₃} → (T₁ → T₂ → T₃) → (T₂ → T₁ → T₃)
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

syntax id(λ x → y) = x ↦ y
