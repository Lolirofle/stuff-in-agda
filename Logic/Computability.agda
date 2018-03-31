module Logic.Computability {ℓ} where

open import Boolean
open import Boolean.Theorems{ℓ}
open import Functional
open import Logic.Properties{ℓ}
open import Logic.Propositional{ℓ}
open import Logic.Propositional.Theorems{ℓ}
open import Relator.Equals{ℓ}
open import Type{ℓ}

-- Existence of a computable function which mirrors the result of whether a proposition is provable or not.
record ComputablyDecidable {X : Type} (φ : X → Stmt) : Stmt where -- TODO: Is this the correct definition?
  field
    predicate : X → Bool
    ⦃ completeness-𝑇 ⦄ : ∀{x} → φ(x)     → (predicate(x) ≡ 𝑇)
    ⦃ completeness-𝐹 ⦄ : ∀{x} → (¬ φ(x)) → (predicate(x) ≡ 𝐹)

-- Existence of a computable function which yields whether a relation between two arguments is provable or not.
record Computable {X Y : Type} (φ : X → Y → Stmt) : Stmt where
  field
    function : X → Y
    ⦃ proof ⦄ : ∀{x}{y} → φ(x)(y) → (function(x) ≡ y)

{-
classicallyComputablyDecidable : ∀{X}{φ} → (∀{x} → Classical(φ(x))) ↔ ComputablyDecidable(φ)
classicallyComputablyDecidable {X}{φ} = [↔]-intro l r where
  l : ComputablyDecidable(φ) → ∀{x} → Classical(φ(x))
  l(decidable) {x} with bivalence -- TODO: Simply not true with the current definition of computably decidable
  ... | true  = classical([∨]-introₗ (ComputablyDecidable.completeness-rev (decidable) {x}))
  ... | false = classical([∨]-introᵣ (ComputablyDecidable.soundness-rev    (decidable) {x}))

  r : (∀{x} → Classical(φ(x))) → ComputablyDecidable(φ)
  ComputablyDecidable.predicate (r(classical(proof))) with proof
  ... | [∨]-introₗ _ = 𝑇
  ... | [∨]-introᵣ _ = 𝐹
  ComputablyDecidable.completeness (r(classical(proof))) = a where postulate a : ∀{a} → a
  ComputablyDecidable.soundness    (r(classical(proof))) = a where postulate a : ∀{a} → a
-}
