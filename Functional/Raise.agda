module Functional.Raise where

open import Functional
import NaturalNumbers as Nat

_⁰ : ∀ {n} {T : Set n} → (T → T) → (T → T)
_⁰ = id

_¹ : ∀ {n} {T : Set n} → (T → T) → (T → T)
_¹ f = f

_² : ∀ {n} {T : Set n} → (T → T) → (T → T)
_² f = f ∘ f

_³ : ∀ {n} {T : Set n} → (T → T) → (T → T)
_³ f = f ∘ f ∘ f

_⁴ : ∀ {n} {T : Set n} → (T → T) → (T → T)
_⁴ f = f ∘ f ∘ f ∘ f

_⁵ : ∀ {n} {T : Set n} → (T → T) → (T → T)
_⁵ f = f ∘ f ∘ f ∘ f ∘ f

_⁶ : ∀ {n} {T : Set n} → (T → T) → (T → T)
_⁶ f = f ∘ f ∘ f ∘ f ∘ f ∘ f

_⁷ : ∀ {n} {T : Set n} → (T → T) → (T → T)
_⁷ f = f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f

_⁸ : ∀ {n} {T : Set n} → (T → T) → (T → T)
_⁸ f = f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f

_⁹ : ∀ {n} {T : Set n} → (T → T) → (T → T)
_⁹ f = f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f

_^_ : ∀ {n} {T : Set n} → (T → T) → Nat.ℕ → (T → T)
_^_ f Nat.ℕ0 = id
_^_ f (Nat.𝑆(n)) = f ∘ (f ^ n)

repeatₗ : ∀ {n} {X Y : Set n} → Nat.ℕ → Y → (Y → X → Y) → X → Y
repeatₗ Nat.ℕ0 null op elem = null
repeatₗ (Nat.𝑆(n)) null op elem = op (repeatₗ n null op elem) elem
-- Example: repeatₗ 3 id (_∘_) f = ((id ∘ f) ∘ f) ∘ f
-- Example in Haskell: (foldl (.) (id) (take 5 (repeat f)))
-- in Haskell: (\n null op elem -> foldl op null (take n (repeat elem))) :: Int -> a -> (b -> a -> b) -> b -> b

repeatᵣ : ∀ {n} {X Y : Set n} → Nat.ℕ → X → (X → Y → Y) → Y → Y
repeatᵣ Nat.ℕ0 elem op null = null
repeatᵣ (Nat.𝑆(n)) elem op null = op elem (repeatᵣ n elem op null)
-- in Haskell: (\n elem op null -> foldr op null (take n (repeat elem))) :: Int -> a -> (a -> b -> b) -> b -> b

-- TODO: curry ∘ curry does not work with repeat because LHS≠RHS, but can this be fixed?
-- curry             :: ((a, b) -> c) -> a -> b -> c
-- curry.curry       :: (((a, b), b1) -> c) -> a -> b -> b1 -> c
-- curry.curry.curry :: ((((a, b), b1), b2) -> c) -> a -> b -> b1 -> b2 -> c
