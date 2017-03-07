module Functional where

id : ∀ {n} {T : Set n} → T → T
id x = x

const : ∀ {n₁ n₂} {T₁ : Set n₁} → {T₂ : Set n₂} → T₁ → (T₂ → T₁)
const x _ = x

apply : ∀ {n₁ n₂} {T₁ : Set n₁} → {T₂ : Set n₂} → T₁ → (T₁ → T₂) → T₂
apply x f = f x

infixl 20 _∘_
_∘_ : ∀ {n₁ n₂ n₃} {X : Set n₁} → {Y : Set n₂} → {Z : Set n₃} → (Y → Z) → (X → Y) → (X → Z)
(f ∘ g) x = f(g(x))

lift : ∀ {n₁ n₂ n₃} {X : Set n₁} → {Y : Set n₂} → {Z : Set n₃} → (X → Y) → ((Z → X) → (Z → Y))
lift f g = f ∘ g

swap : ∀ {n₁ n₂ n₃} {T₁ : Set n₁} → {T₂ : Set n₂} → {T₃ : Set n₃} → (T₁ → T₂ → T₃) → (T₂ → T₁ → T₃)
swap f x₂ x₁ = f x₁ x₂

-- 🔁(f ∘ 2)
