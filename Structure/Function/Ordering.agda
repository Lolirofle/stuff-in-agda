import      Lvl
open import Type

module Structure.Function.Ordering where

open import Logic
open import Logic.Propositional

module _ {ℓₒ₁ ℓₒ₂} {T₁ : Type{ℓₒ₁}} {T₂ : Type{ℓₒ₂}} (_≤₁_ : T₁ → T₁ → Type{ℓₒ₁}) (_≤₂_ : T₂ → T₂ → Type{ℓₒ₂}) where
  Increasing : (T₁ → T₂) → Stmt
  Increasing(f) = (∀{a b : T₁} → (a ≤₁ b) → (f(a) ≤₂ f(b)))

  Decreasing : (T₁ → T₂) → Stmt
  Decreasing(f) = (∀{a b : T₁} → (a ≤₁ b) → (f(b) ≤₂ f(a)))

  Monotone : (T₁ → T₂) → Stmt
  Monotone(f) = (Increasing(f) ∨ Decreasing(f))
