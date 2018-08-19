module Logic.Computability {ℓₗ}{ℓₒ} where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Proofs{ℓₗ Lvl.⊔ ℓₒ}
open import Functional
open import Logic.Classical{ℓₗ Lvl.⊔ ℓₒ}
open import Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ}
open import Logic.Propositional.Theorems{ℓₗ Lvl.⊔ ℓₒ}
open import Relator.Equals{ℓₗ Lvl.⊔ ℓₒ}
open import Type{ℓₒ}

-- TODO: Maybe instead define (decide computablyDecides φ)?

record SemiComputablyDecidable {X : Type} (φ : X → Stmt) : Stmt where
  constructor SemiComputablyDecidable-intro
  field
    decide : X → Bool
    ⦃ completeness-𝑇 ⦄ : ∀{x} → φ(x)     → (decide(x) ≡ 𝑇)
    ⦃ completeness-𝐹 ⦄ : ∀{x} → (¬ φ(x)) → (decide(x) ≡ 𝐹)

  soundness-𝐹 : ∀{x} → (¬ φ(x)) ← (decide(x) ≡ 𝐹)
  soundness-𝐹 = (contrapositiveᵣ(completeness-𝑇)) ∘ ([↔]-elimₗ [≢][𝑇]-is-[𝐹])

-- Existence of a computable function which mirrors the result of whether a proposition is provable or not.
record ComputablyDecidable {X : Type} (φ : X → Stmt) : Stmt where -- TODO: Is this the correct definition?
  constructor ComputablyDecidable-intro
  field
    decide : X → Bool
    ⦃ proof ⦄ : ∀{x} → φ(x) ↔ (decide(x) ≡ 𝑇)

  soundness-𝑇 : ∀{x} → φ(x) ← (decide(x) ≡ 𝑇)
  soundness-𝑇 = [↔]-elimₗ (proof)

  completeness-𝑇 : ∀{x} → φ(x) → (decide(x) ≡ 𝑇)
  completeness-𝑇 = [↔]-elimᵣ (proof)

  soundness-𝐹 : ∀{x} → (¬ φ(x)) ← (decide(x) ≡ 𝐹)
  soundness-𝐹 = (contrapositiveᵣ(completeness-𝑇)) ∘ ([↔]-elimₗ [≢][𝑇]-is-[𝐹])

  completeness-𝐹 : ∀{x} → (¬ φ(x)) → (decide(x) ≡ 𝐹)
  completeness-𝐹 = ([↔]-elimᵣ [≢][𝑇]-is-[𝐹]) ∘ (contrapositiveᵣ(soundness-𝑇))

  instance
    semi : SemiComputablyDecidable(φ)
    semi =
      record{
        decide      = decide ;
        completeness-𝑇 = completeness-𝑇 ;
        completeness-𝐹 = completeness-𝐹
      }

  instance
    classical : ∀{x} → Classical(φ(x))
    classical {x} with bivalence
    ... | [∨]-introₗ(≡𝑇) = classical-intro ⦃ [∨]-introₗ (soundness-𝑇 {x} (≡𝑇)) ⦄
    ... | [∨]-introᵣ(≡𝐹) = classical-intro ⦃ [∨]-introᵣ (soundness-𝐹 {x} (≡𝐹)) ⦄

classicalIsComputablyDecidable : ∀{X}{φ : X → Stmt} → (∀{x} → Classical(φ(x))) ↔ ComputablyDecidable(φ)
classicalIsComputablyDecidable {X}{φ} = [↔]-intro (ComputablyDecidable.classical) r where
  decider : (∀{x} → Classical(φ(x))) → X → Bool
  decider(classic)(x) with Classical.excluded-middle(classic{x})
  ... | [∨]-introₗ _ = 𝑇
  ... | [∨]-introᵣ _ = 𝐹

  r : (∀{x} → Classical(φ(x))) → ComputablyDecidable(φ)
  ComputablyDecidable.decide (r(classic)) = decider(classic)
  ComputablyDecidable.proof (r(classic)) {x} = [↔]-intro rl rr where
    rl : ∀{x} → φ(x) ← (decider(classic)(x) ≡ 𝑇)
    rl {x} decider𝑇 with Classical.excluded-middle(classic{x})
    ... | [∨]-introₗ (φx)  = φx
    ... | [∨]-introᵣ (¬φx) = [⊥]-elim(disjointness([∧]-intro decider𝑇 [≡]-intro))

    rr : ∀{x} → φ(x) → (decider(classic)(x) ≡ 𝑇)
    rr {x} (φx₂) with Classical.excluded-middle(classic{x})
    ... | [∨]-introₗ (φx)  = [≡]-intro
    ... | [∨]-introᵣ (¬φx) = [⊥]-elim(¬φx φx₂)



-- Existence of a computable function which yields whether a relation between two arguments is provable or not.
-- TODO: Is this neccessary to have? Compare with Functional.Proofs.function
record Computable {X Y : Type} (φ : X → Y → Stmt) : Stmt where
  field
    function : X → Y
    ⦃ proof ⦄ : ∀{x}{y} → φ(x)(y) → (function(x) ≡ y)
