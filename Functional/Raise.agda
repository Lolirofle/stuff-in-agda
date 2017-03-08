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
