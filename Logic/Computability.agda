module Logic.Computability {ℓ} where

open import Boolean
open import Logic.Propositional{ℓ}
open import Relator.Equals{ℓ}
open import Type{ℓ}

-- Existence of a computable function which mirrors the result of whether a proposition is provable or not.
record ComputablyDecidable {X : Type} (φ : X → Stmt) : Stmt where
  field
    compute : X → Bool
    ⦃ positive-proof ⦄ : ∀{x} → φ(x)     → (compute(x) ≡ 𝑇)
    ⦃ negative-proof ⦄ : ∀{x} → (¬ φ(x)) → (compute(x) ≡ 𝐹)

-- Existence of a computable function which yields whether a relation between two arguments is provable or not.
record Computable {X Y : Type} (φ : X → Y → Stmt) : Stmt where
  field
    compute : X → Y
    ⦃ proof ⦄ : ∀{x}{y} → φ(x)(y) → (compute(x) ≡ y)

-- classicallyComputablyDecidable : ∀{X}{φ} → (∀{x} → Classical(φ(x))) → ComputablyDecidable(φ) → (∀{x} → φ(x) ↔ (compute(x) ≡ 𝑇))
