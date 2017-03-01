module Functional where

id : ∀ {n} {T : Set n} → T → T
id x = x

const : ∀ {n₁ n₂} {T₁ : Set n₁} → {T₂ : Set n₂} → T₁ → (T₂ → T₁)
const x _ = x

infixl 20 _∘_
_∘_ : ∀ {n₁ n₂ n₃} {X : Set n₁} → {Y : Set n₂} → {Z : Set n₃} → (Y → Z) → (X → Y) → (X → Z)
(f ∘ g) x = f(g(x))
