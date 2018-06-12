module Logic.Computability {ℓ} where

open import Data.Boolean
open import Data.Boolean.Proofs{ℓ}
open import Functional
open import Logic.Properties{ℓ}
open import Logic.Propositional{ℓ}
open import Logic.Propositional.Theorems{ℓ}
open import Relator.Equals{ℓ}
open import Type{ℓ}

record SemiComputablyDecidable {X : Type} (φ : X → Stmt) : Stmt where
  field
    predicate : X → Bool
    ⦃ completeness-𝑇 ⦄ : ∀{x} → φ(x)     → (predicate(x) ≡ 𝑇)
    ⦃ completeness-𝐹 ⦄ : ∀{x} → (¬ φ(x)) → (predicate(x) ≡ 𝐹)

-- Existence of a computable function which mirrors the result of whether a proposition is provable or not.
record ComputablyDecidable {X : Type} (φ : X → Stmt) : Stmt where -- TODO: Is this the correct definition?
  field
    predicate : X → Bool
    ⦃ proof ⦄ : ∀{x} → φ(x) ↔ (predicate(x) ≡ 𝑇)

  soundness-𝑇 : ∀{x} → φ(x) ← (predicate(x) ≡ 𝑇)
  soundness-𝑇 = [↔]-elimₗ (proof)

  completeness-𝑇 : ∀{x} → φ(x) → (predicate(x) ≡ 𝑇)
  completeness-𝑇 = [↔]-elimᵣ (proof)

  soundness-𝐹 : ∀{x} → (¬ φ(x)) ← (predicate(x) ≡ 𝐹)
  soundness-𝐹 = (contrapositiveᵣ(completeness-𝑇)) ∘ ([↔]-elimₗ [≢][𝑇]-is-[𝐹])

  completeness-𝐹 : ∀{x} → (¬ φ(x)) → (predicate(x) ≡ 𝐹)
  completeness-𝐹 = ([↔]-elimᵣ [≢][𝑇]-is-[𝐹]) ∘ (contrapositiveᵣ(soundness-𝑇))

  semi : SemiComputablyDecidable(φ)
  semi =
    record{
      predicate      = predicate ;
      completeness-𝑇 = completeness-𝑇 ;
      completeness-𝐹 = completeness-𝐹
    }

-- Existence of a computable function which yields whether a relation between two arguments is provable or not.
record Computable {X Y : Type} (φ : X → Y → Stmt) : Stmt where
  field
    function : X → Y
    ⦃ proof ⦄ : ∀{x}{y} → φ(x)(y) → (function(x) ≡ y)


classicalIsComputablyDecidable : ∀{X}{φ : X → Stmt} → (∀{x} → Classical(φ(x))) ↔ ComputablyDecidable(φ)
classicalIsComputablyDecidable {X}{φ} = [↔]-intro l r where
  l : ComputablyDecidable(φ) → ∀{x} → Classical(φ(x))
  l(decidable) {x} with bivalence
  ... | [∨]-introₗ(≡𝑇) = classical ⦃ [∨]-introₗ (ComputablyDecidable.soundness-𝑇 (decidable) {x} (≡𝑇)) ⦄
  ... | [∨]-introᵣ(≡𝐹) = classical ⦃ [∨]-introᵣ (ComputablyDecidable.soundness-𝐹 (decidable) {x} (≡𝐹)) ⦄

  decider : (∀{x} → Classical(φ(x))) → X → Bool
  decider(classic)(x) with Classical.proof(classic{x})
  ... | [∨]-introₗ _ = 𝑇
  ... | [∨]-introᵣ _ = 𝐹

  r : (∀{x} → Classical(φ(x))) → ComputablyDecidable(φ)
  ComputablyDecidable.predicate (r(classic)) = decider(classic)
  ComputablyDecidable.proof (r(classic)) {x} = [↔]-intro rl rr where
    postulate a : ∀{a} → a -- TODO

    rl : ∀{x} → φ(x) ← (decider(classic)(x) ≡ 𝑇)
    rl {x} _ with Classical.proof(classic{x})
    ... | [∨]-introₗ (φx)  = φx
    ... | [∨]-introᵣ (¬φx) = a

    rr : ∀{x} → φ(x) → (decider(classic)(x) ≡ 𝑇)
    rr {x} (φx) = a

