-- TODO: Maybe rename this to "function iteration"
module Functional.Repeat where

open import Functional
open import Numeral.Natural
open import Type

module _ {ℓ} {T : Type{ℓ}} where
  _⁰ : (T → T) → (T → T)
  _⁰ = id

  _¹ : (T → T) → (T → T)
  _¹ f = f

  _² : (T → T) → (T → T)
  _² f = f ∘ f

  _³ : (T → T) → (T → T)
  _³ f = f ∘ f ∘ f

  _⁴ : (T → T) → (T → T)
  _⁴ f = f ∘ f ∘ f ∘ f

  _⁵ : (T → T) → (T → T)
  _⁵ f = f ∘ f ∘ f ∘ f ∘ f

  _⁶ : (T → T) → (T → T)
  _⁶ f = f ∘ f ∘ f ∘ f ∘ f ∘ f

  _⁷ : (T → T) → (T → T)
  _⁷ f = f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f

  _⁸ : (T → T) → (T → T)
  _⁸ f = f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f

  _⁹ : (T → T) → (T → T)
  _⁹ f = f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f ∘ f

  -- Repeated function composition
  -- Example:
  --   f ^ 0 = id
  --   f ^ 1 = f
  --   f ^ 2 = f ∘ f
  --   f ^ 3 = f ∘ f ∘ f
  --   f ^ 4 = f ∘ f ∘ f ∘ f
  _^_ : (T → T) → ℕ → (T → T)
  _^_ f 𝟎      = id
  _^_ f (𝐒(n)) = f ∘ (f ^ n)

module _ {ℓ₁}{ℓ₂} {X : Type{ℓ₁}} {Y : Type{ℓ₂}} where
  -- Repeat a binary operation n times for the same element and an initial element
  -- Example: repeatₗ 3 id (_∘_) f = ((id ∘ f) ∘ f) ∘ f
  -- Example in Haskell: (foldl (.) (id) (take 5 (repeat f)))
  -- Implementation in Haskell: (\n null op elem -> foldl op null (take n (repeat elem))) :: Int -> a -> (b -> a -> b) -> b -> b
  repeatₗ : ℕ → (Y → X → Y) → (Y → X → Y)
  repeatₗ n (_▫_) null elem = ((_▫ elem) ^ n) (null)

  -- Repeat a binary operation n times for the same element and an initial element
  -- Example: repeatᵣ 3 id (_∘_) f = f ∘ (f ∘ (f ∘ id))
  -- Implementation in Haskell: (\n elem op null -> foldr op null (take n (repeat elem))) :: Int -> a -> (a -> b -> b) -> b -> b
  repeatᵣ : ℕ → (X → Y → Y) → (X → Y → Y)
  repeatᵣ n (_▫_) elem = (elem ▫_) ^ n

module _ {ℓ} {X : Type{ℓ}} where
  -- Repeat a binary operation n times for the same element and using the default element on zero.
  -- Examples:
  --   repeatₗ 0 def (_∘_) f = def
  --   repeatₗ 4 def (_∘_) f = ((f ∘ f) ∘ f) ∘ f
  repeatₗ-default : ℕ → (X → X → X) → (X → X → X)
  repeatₗ-default 𝟎      _     def  _    = def
  repeatₗ-default (𝐒(n)) (_▫_) _    elem = repeatₗ(n) (_▫_) elem elem

  -- Repeat a binary operation n times for the same element and using the default element on zero.
  -- Examples:
  --   repeatᵣ 0 f (_∘_) def = def
  --   repeatᵣ 4 f (_∘_) def = f ∘ (f ∘ (f ∘ f))
  repeatᵣ-default : ℕ → (X → X → X) → (X → X → X)
  repeatᵣ-default 𝟎      _     _    def  = def
  repeatᵣ-default (𝐒(n)) (_▫_) elem _    = repeatᵣ(n) (_▫_) elem elem

  -- TODO: curry ∘ curry does not work with repeat because LHS≠RHS, but can this be fixed?
  -- curry             :: ((a, b) -> c) -> a -> b -> c
  -- curry.curry       :: (((a, b), b1) -> c) -> a -> b -> b1 -> c
  -- curry.curry.curry :: ((((a, b), b1), b2) -> c) -> a -> b -> b1 -> b2 -> c

  -- (b → c) → ((a → b) → (a → c))
  -- (((x , y) , z) → t) → (x → (y → (z → t)))
