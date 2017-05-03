module Functional.Raise where

open import Functional
import Numeral.Natural as Nat

_⁰ : ∀{n} {T : Set n} → (T → T) → (T → T)
_⁰ = id

_¹ : ∀{n} {T : Set n} → (T → T) → (T → T)
_¹ f = f

_² : ∀{n} {T : Set n} → (T → T) → (T → T)
_² f = f ∘ f

_³ : ∀{n} {T : Set n} → (T → T) → (T → T)
_³ f = f ∘ f ∘ f

_⁴ : ∀{n} {T : Set n} → (T → T) → (T → T)
_⁴ f = f ∘ f ∘ f ∘ f

_⁵ : ∀{n} {T : Set n} → (T → T) → (T → T)
_⁵ f = f ∘ f ∘ f ∘ f ∘ f

_⁶ : ∀{n} {T : Set n} → (T → T) → (T → T)
_⁶ f = f ∘ f ∘ f ∘ f ∘ f ∘ f

_⁷ : ∀{n} {T : Set n} → (T → T) → (T → T)
_⁷ f = f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f

_⁸ : ∀{n} {T : Set n} → (T → T) → (T → T)
_⁸ f = f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f

_⁹ : ∀{n} {T : Set n} → (T → T) → (T → T)
_⁹ f = f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f

-- Repeated function composition
_^_ : ∀{n} {T : Set n} → (T → T) → Nat.ℕ → (T → T)
_^_ f Nat.𝟎 = id
_^_ f (Nat.𝐒(n)) = f ∘ (f ^ n)

-- Repeat a binary operation n times for the same element and a initial element
repeatₗ : ∀{n} {X Y : Set n} → Nat.ℕ → Y → (Y → X → Y) → X → Y
repeatₗ  Nat.𝟎     null _▫_ elem = null
repeatₗ (Nat.𝐒(n)) null _▫_ elem = (repeatₗ n null _▫_ elem) ▫ elem
-- Example: repeatₗ 3 id (_∘_) f = ((id ∘ f) ∘ f) ∘ f
-- Example in Haskell: (foldl (.) (id) (take 5 (repeat f)))
-- in Haskell: (\n null op elem -> foldl op null (take n (repeat elem))) :: Int -> a -> (b -> a -> b) -> b -> b

-- Repeat a binary operation n times for the same element and a initial element
repeatᵣ : ∀{n} {X Y : Set n} → Nat.ℕ → X → (X → Y → Y) → Y → Y
repeatᵣ  Nat.𝟎     elem _▫_ null = null
repeatᵣ (Nat.𝐒(n)) elem _▫_ null = elem ▫ (repeatᵣ n elem _▫_ null)
-- Example: repeatᵣ 3 id (_∘_) f = id ∘ (f ∘ (f ∘ f))
-- in Haskell: (\n elem op null -> foldr op null (take n (repeat elem))) :: Int -> a -> (a -> b -> b) -> b -> b

-- TODO: curry ∘ curry does not work with repeat because LHS≠RHS, but can this be fixed?
-- curry             :: ((a, b) -> c) -> a -> b -> c
-- curry.curry       :: (((a, b), b1) -> c) -> a -> b -> b1 -> c
-- curry.curry.curry :: ((((a, b), b1), b2) -> c) -> a -> b -> b1 -> b2 -> c

-- (b → c) → ((a → b) → (a → c))
-- (((x , y) , z) → t) → (x → (y → (z → t)))


-- repeatᵣ₂ : ∀{n} {X Y : Set n} → Nat.ℕ → X → (X → Y → Y) → Y → Y
-- repeatᵣ₂  Nat.𝟎     elem _▫_ null = null
-- repeatᵣ₂ (Nat.𝐒(n)) elem _▫_ null = elem ▫ (repeatᵣ₂ n elem _▫_ null)

-- (T(a,b) → z) → U(a,U(b,U(c)))
-- (T(T(a,b),c) → z) → U(a,U(b,U(c,U(z))))

-- (T₁(a₁,b₁) → z₁) → U₁(a₁,U₁(b₁,U₁(c₁)))
-- (T₂(a₂,b₂) → z₂) → U₂(a₂,U₂(b₂,U₂(c₂)))
-- ((B → C) ⨯ (A → B)) → (A → C)
--   (T₁(a₁,b₁) → z₁) = U₂(a₂,U₂(b₂,U₂(c₂)))
--   (T₁(a₁,b₁) → z₁) = U₂(a₂,U₂(b₂,U₂(c₂))) -- U₂=
-- ((B → C) ⨯ (A → B)) → (A → C)

