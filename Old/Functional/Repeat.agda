module Functional.Repeat{ℓ} where

open import Functional
open import Numeral.Natural
open import Type{ℓ}

_⁰ : ∀{T : Type} → (T → T) → (T → T)
_⁰ = id

_¹ : ∀{T : Type} → (T → T) → (T → T)
_¹ f = f

_² : ∀{T : Type} → (T → T) → (T → T)
_² f = f ∘ f

_³ : ∀{T : Type} → (T → T) → (T → T)
_³ f = f ∘ f ∘ f

_⁴ : ∀{T : Type} → (T → T) → (T → T)
_⁴ f = f ∘ f ∘ f ∘ f

_⁵ : ∀{T : Type} → (T → T) → (T → T)
_⁵ f = f ∘ f ∘ f ∘ f ∘ f

_⁶ : ∀{T : Type} → (T → T) → (T → T)
_⁶ f = f ∘ f ∘ f ∘ f ∘ f ∘ f

_⁷ : ∀{T : Type} → (T → T) → (T → T)
_⁷ f = f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f

_⁸ : ∀{T : Type} → (T → T) → (T → T)
_⁸ f = f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f

_⁹ : ∀{T : Type} → (T → T) → (T → T)
_⁹ f = f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f

-- Repeated function composition
-- Example:
--   f ^ 0 = id
--   f ^ 1 = f
--   f ^ 2 = f ∘ f
--   f ^ 3 = f ∘ f ∘ f
--   f ^ 4 = f ∘ f ∘ f ∘ f
_^_ : ∀{T : Type} → (T → T) → ℕ → (T → T)
_^_ f 𝟎      = id
_^_ f (𝐒(n)) = f ∘ (f ^ n)

-- Repeat a binary operation n times for the same element and a initial element
--   Example: repeatₗ 3 id (_∘_) f = ((id ∘ f) ∘ f) ∘ f
--   Example in Haskell: (foldl (.) (id) (take 5 (repeat f)))
--   Implementation in Haskell: (\n null op elem -> foldl op null (take n (repeat elem))) :: Int -> a -> (b -> a -> b) -> b -> b
repeatₗ : ∀{X Y : Type} → ℕ → (Y → X → Y) → Y → X → Y
repeatₗ  𝟎     (_▫_) null elem = null
repeatₗ (𝐒(n)) (_▫_) null elem = (repeatₗ n (_▫_) null elem) ▫ elem

-- Repeat a binary operation n times for the same element and a initial element
--   Example: repeatᵣ 3 id (_∘_) f = f ∘ (f ∘ (f ∘ id))
--   Implementation in Haskell: (\n elem op null -> foldr op null (take n (repeat elem))) :: Int -> a -> (a -> b -> b) -> b -> b
repeatᵣ : ∀{X Y : Type} → ℕ → (X → Y → Y) → X → Y → Y
repeatᵣ  𝟎     (_▫_) elem null = null
repeatᵣ (𝐒(n)) (_▫_) elem null = elem ▫ (repeatᵣ n (_▫_) elem null)

-- TODO: curry ∘ curry does not work with repeat because LHS≠RHS, but can this be fixed?
-- curry             :: ((a, b) -> c) -> a -> b -> c
-- curry.curry       :: (((a, b), b1) -> c) -> a -> b -> b1 -> c
-- curry.curry.curry :: ((((a, b), b1), b2) -> c) -> a -> b -> b1 -> b2 -> c

-- (b → c) → ((a → b) → (a → c))
-- (((x , y) , z) → t) → (x → (y → (z → t)))


-- repeatᵣ₂ : ∀{X Y : Type} → ℕ → X → (X → Y → Y) → Y → Y
-- repeatᵣ₂  𝟎     elem _▫_ null = null
-- repeatᵣ₂ (𝐒(n)) elem _▫_ null = elem ▫ (repeatᵣ₂ n elem _▫_ null)

-- (T(a,b) → z) → U(a,U(b,U(c)))
-- (T(T(a,b),c) → z) → U(a,U(b,U(c,U(z))))

-- (T₁(a₁,b₁) → z₁) → U₁(a₁,U₁(b₁,U₁(c₁)))
-- (T₂(a₂,b₂) → z₂) → U₂(a₂,U₂(b₂,U₂(c₂)))
-- ((B → C) ⨯ (A → B)) → (A → C)
--   (T₁(a₁,b₁) → z₁) = U₂(a₂,U₂(b₂,U₂(c₂)))
--   (T₁(a₁,b₁) → z₁) = U₂(a₂,U₂(b₂,U₂(c₂))) -- U₂=
-- ((B → C) ⨯ (A → B)) → (A → C)
