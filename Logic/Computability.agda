module Logic.Computability where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Stmt using (IsTrue)
import      Data.Boolean.Stmt.Proofs as BooleanStmt
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Boolean.Proofs
open import Functional
open import Logic
open import Logic.Classical hiding (decide)
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

-- TODO: Maybe instead define (decide computablyDecides P)?

record SemiComputablyDecidable {ℓ₁}{ℓ₂} {X : Type{ℓ₁}} (P : X → Stmt{ℓ₂}) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
  constructor intro
  field
    decide : X → Bool

  field
    completeness-𝑇 : ∀{x} → P(x)     → (decide(x) ≡ 𝑇)
    completeness-𝐹 : ∀{x} → (¬ P(x)) → (decide(x) ≡ 𝐹)

  soundness-𝐹 : ∀{x} → (¬ P(x)) ← (decide(x) ≡ 𝐹)
  soundness-𝐹 = (contrapositiveᵣ(completeness-𝑇)) ∘ ([↔]-to-[←] [≢][𝑇]-is-[𝐹])

-- Existence of a computable function which mirrors the result of whether a proposition is provable or not.
record ComputablyDecidable {ℓ₁}{ℓ₂} {X : Type{ℓ₁}} (P : X → Stmt{ℓ₂}) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
  constructor intro
  field
    decide : X → Bool
    ⦃ proof ⦄ : ∀{x} → P(x) ↔ (decide(x) ≡ 𝑇)

  proof-istrue : ∀{x} → P(x) ↔ IsTrue(decide(x))
  proof-istrue = [↔]-transitivity proof ([↔]-symmetry BooleanStmt.IsTrue.is-𝑇)

  soundness-𝑇 : ∀{x} → P(x) ← (decide(x) ≡ 𝑇)
  soundness-𝑇 = [↔]-to-[←] (proof)

  completeness-𝑇 : ∀{x} → P(x) → (decide(x) ≡ 𝑇)
  completeness-𝑇 = [↔]-to-[→] (proof)

  soundness-𝐹 : ∀{x} → (¬ P(x)) ← (decide(x) ≡ 𝐹)
  soundness-𝐹 = (contrapositiveᵣ(completeness-𝑇)) ∘ ([↔]-to-[←] [≢][𝑇]-is-[𝐹])

  completeness-𝐹 : ∀{x} → (¬ P(x)) → (decide(x) ≡ 𝐹)
  completeness-𝐹 = ([↔]-to-[→] [≢][𝑇]-is-[𝐹]) ∘ (contrapositiveᵣ(soundness-𝑇))

  instance
    semi : SemiComputablyDecidable(P)
    semi =
      record{
        decide      = decide ;
        completeness-𝑇 = completeness-𝑇 ;
        completeness-𝐹 = completeness-𝐹
      }

  instance
    classical : ∀{x} → Classical(P(x))
    classical {x} with bivalence
    ... | [∨]-introₗ(≡𝑇) = intro ⦃ [∨]-introₗ (soundness-𝑇 {x} (≡𝑇)) ⦄
    ... | [∨]-introᵣ(≡𝐹) = intro ⦃ [∨]-introᵣ (soundness-𝐹 {x} (≡𝐹)) ⦄

  negation : ComputablyDecidable(¬_ ∘ P)
  decide (negation) (x) = !(decide(x))
  proof  (negation) {x} = [↔]-intro (soundness-𝐹{_} ∘ l{_}) (r{_} ∘ completeness-𝐹{_}) where
    l : ∀{b} → (b ≡ 𝐹) ← (! b ≡ 𝑇)
    l proof = (symmetry(_≡_) (Data.Boolean.Proofs.[!!]-elim {_})) 🝖 [≡]-with(!) (proof)

    r : ∀{b} → (b ≡ 𝐹) → (! b ≡ 𝑇)
    r = [≡]-with(!)

module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}} {P₁ : X → Stmt{ℓ₂}} {P₂ : X → Stmt{ℓ₃}} where
  open ComputablyDecidable

  ComputablyDecidable-conjunction : ⦃ _ : ComputablyDecidable(P₁) ⦄ → ⦃ _ : ComputablyDecidable(P₂) ⦄ → ComputablyDecidable(x ↦ P₁(x) ∧ P₂(x))
  decide (ComputablyDecidable-conjunction ⦃ comp₁ ⦄ ⦃ comp₂ ⦄) (x) = decide(comp₁)(x) && decide(comp₂)(x)
  proof  (ComputablyDecidable-conjunction ⦃ comp₁ ⦄ ⦃ comp₂ ⦄) {x} = [↔]-intro (l) (r) where
    l : (P₁(x) ∧ P₂(x)) ← (decide(comp₁)(x) && decide(comp₂)(x) ≡ 𝑇)
    l(truth) =
      ([∧]-intro
        ([↔]-to-[←] (proof(comp₁)) (𝑇.[∧]-elimₗ truth))
        ([↔]-to-[←] (proof(comp₂)) (𝑇.[∧]-elimᵣ truth))
      )

    r : (P₁(x) ∧ P₂(x)) → (decide(comp₁)(x) && decide(comp₂)(x) ≡ 𝑇)
    r([∧]-intro P₁x P₂x) =
      (𝑇.[∧]-intro
        ([↔]-to-[→] (proof(comp₁)) (P₁x))
        ([↔]-to-[→] (proof(comp₂)) (P₂x))
      )

  ComputablyDecidable-disjunction : ⦃ _ : ComputablyDecidable(P₁) ⦄ → ⦃ _ : ComputablyDecidable(P₂) ⦄ → ComputablyDecidable(x ↦ P₁(x) ∨ P₂(x))
  decide (ComputablyDecidable-disjunction ⦃ comp₁ ⦄ ⦃ comp₂ ⦄) (x) = decide(comp₁)(x) || decide(comp₂)(x)
  proof  (ComputablyDecidable-disjunction ⦃ comp₁ ⦄ ⦃ comp₂ ⦄) {x} = [↔]-intro (l) (r) where
    l : (P₁(x) ∨ P₂(x)) ← (decide(comp₁)(x) || decide(comp₂)(x) ≡ 𝑇)
    l(truth) =
      (𝑇.[∨]-elim
        (truthpart ↦ [∨]-introₗ ([↔]-to-[←] (proof(comp₁))(truthpart)))
        (truthpart ↦ [∨]-introᵣ ([↔]-to-[←] (proof(comp₂))(truthpart)))
        (truth)
      )

    r : (P₁(x) ∨ P₂(x)) → (decide(comp₁)(x) || decide(comp₂)(x) ≡ 𝑇)
    r(truth) =
      ([∨]-elim
        (truthpart ↦ 𝑇.[∨]-introₗ ([↔]-to-[→] (proof(comp₁))(truthpart)))
        (truthpart ↦ 𝑇.[∨]-introᵣ ([↔]-to-[→] (proof(comp₂))(truthpart)))
        (truth)
      )

    -- ComputablyDecidable-implication : ComputablyDecidable(P₁) → ComputablyDecidable(P₂) → ComputablyDecidable(P₁ → P₂)
    -- ComputablyDecidable-equivalence : ComputablyDecidable(P₁) → ComputablyDecidable(P₂) → ComputablyDecidable(P₁ ↔ P₂)

module _ {ℓ₁ ℓ₂} {X : Type{ℓ₁}} {P : X → Stmt{ℓ₂}} where
  classicalIsComputablyDecidable : (∀{x} → Classical(P(x))) ↔ ComputablyDecidable(P)
  classicalIsComputablyDecidable = [↔]-intro (ComputablyDecidable.classical) r where
    decider : (∀{x} → Classical(P(x))) → X → Bool
    decider(classic)(x) = Classical.decide(classic{x})

    r : (∀{x} → Classical(P(x))) → ComputablyDecidable(P)
    ComputablyDecidable.decide (r(classic)) = decider(classic)
    ComputablyDecidable.proof (r(classic)) {x} = [↔]-intro rl rr where
      rl : ∀{x} → P(x) ← (decider(classic)(x) ≡ 𝑇)
      rl {x} decider𝑇 with Classical.excluded-middle(classic{x})
      ... | [∨]-introₗ (Px)  = Px
      ... | [∨]-introᵣ (¬Px) = [⊥]-elim(disjointness([∧]-intro decider𝑇 [≡]-intro))

      rr : ∀{x} → P(x) → (decider(classic)(x) ≡ 𝑇)
      rr {x} (Px₂) with Classical.excluded-middle(classic{x})
      ... | [∨]-introₗ (Px)  = [≡]-intro
      ... | [∨]-introᵣ (¬Px) = [⊥]-elim(¬Px Px₂)



-- Existence of a computable function which yields whether a relation between two arguments is provable or not.
-- TODO: Is this neccessary to have? Compare with Function.Proofs.function
record Computable {ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}}{Y : Type{ℓ₂}} (P : X → Y → Stmt{ℓ₃}) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
  field
    function : X → Y

  field
    proof : ∀{x}{y} → P(x)(y) → (function(x) ≡ y)
