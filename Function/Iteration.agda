module Function.Iteration where

open import Data
open import Functional
open import Numeral.Natural
open import Numeral.Natural.Induction
open import Type
open import Syntax.Number

module _ {ℓ} {T : Type{ℓ}} where
  -- Repeated function composition
  -- Example:
  --   f ^ 0 = id
  --   f ^ 1 = f
  --   f ^ 2 = f ∘ f
  --   f ^ 3 = f ∘ f ∘ f
  --   f ^ 4 = f ∘ f ∘ f ∘ f
  -- Alternative implementation:
  --   _^_ f 𝟎      = id
  --   _^_ f (𝐒(n)) = f ∘ (f ^ n)
  _^_ : (T → T) → ℕ → (T → T)
  _^_ f = ℕ-elim _ id (const(f ∘_))

  _⁰ : (T → T) → (T → T)
  _⁰ = _^ 0

  _¹ : (T → T) → (T → T)
  _¹ = _^ 1

  _² : (T → T) → (T → T)
  _² = _^ 2

  _³ : (T → T) → (T → T)
  _³ = _^ 3

  _⁴ : (T → T) → (T → T)
  _⁴ = _^ 4

  _⁵ : (T → T) → (T → T)
  _⁵ = _^ 5

  _⁶ : (T → T) → (T → T)
  _⁶ = _^ 6

  _⁷ : (T → T) → (T → T)
  _⁷ = _^ 7

  _⁸ : (T → T) → (T → T)
  _⁸ = _^ 8

  _⁹ : (T → T) → (T → T)
  _⁹ = _^ 9

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
  --   repeatₗ 1 def (_∘_) f = f
  --   repeatₗ 4 def (_∘_) f = ((f ∘ f) ∘ f) ∘ f
  repeatₗ-default : ℕ → (X → X → X) → X → (X → X)
  repeatₗ-default 𝟎     _     def  _    = def
  repeatₗ-default(𝐒(n)) (_▫_) _    elem = repeatₗ(n) (_▫_) elem elem

  -- Repeat a binary operation n times for the same element and using the default element on zero.
  -- Examples:
  --   repeatᵣ 0 f (_∘_) def = def
  --   repeatᵣ 1 f (_∘_) def = f
  --   repeatᵣ 4 f (_∘_) def = f ∘ (f ∘ (f ∘ f))
  repeatᵣ-default : ℕ → (X → X → X) → X → (X → X)
  repeatᵣ-default 𝟎      _     _    def = def
  repeatᵣ-default (𝐒(n)) (_▫_) elem _   = repeatᵣ(n) (_▫_) elem elem
