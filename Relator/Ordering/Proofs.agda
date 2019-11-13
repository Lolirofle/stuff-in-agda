module Relator.Ordering.Proofs where

open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Type
import      Relator.Ordering
open import Structure.Relator.Ordering
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Transitivity

module From-[≤] {ℓ₁ ℓ₂} {T : Type{ℓ₁}} (_≤_ : T → T → Stmt{ℓ₂}) where
  open        Relator.Ordering.From-[≤] (_≤_)
  open import Sets.Setoid

  module _ ⦃ _ : Equiv(T) ⦄ ⦃ _ : Weak.TotalOrder(_≤_)(_≡_) ⦄ ⦃ _ : (_≡_) ⊆₂ (_≤_) ⦄ where
    [≡]-to-[≥] : Names.Subrelation(_≡_)(_≥_)
    [≡]-to-[≥] = subrelation(_≡_)(_≤_) ∘ symmetry(_≡_)

    [<]-to-[≤] : Names.Subrelation(_<_)(_≤_)
    [<]-to-[≤] {a} {b} nba with converseTotal(_≤_){a}{b}
    [<]-to-[≤] {a} {b} nba | [∨]-introₗ ab = ab
    [<]-to-[≤] {a} {b} nba | [∨]-introᵣ ba = [⊥]-elim(nba ba)

    [>]-to-[≥] : Names.Subrelation(_>_)(_≥_)
    [>]-to-[≥] {a} {b} nba with converseTotal(_≤_){b}{a}
    [>]-to-[≥] {a} {b} nba | [∨]-introₗ ab = ab
    [>]-to-[≥] {a} {b} nba | [∨]-introᵣ ba = [⊥]-elim(nba ba)

    [≤][>]-not : ∀{a b} → (a ≤ b) → (a > b) → ⊥
    [≤][>]-not p q = q p

    [≥][<]-not : ∀{a b} → (a ≥ b) → (a < b) → ⊥
    [≥][<]-not p q = q p

    module _ ([≡]-decidable : ∀{a b : T} → (a ≡ b) ∨ (a ≢ b)) where
      [≤]-or-[>] : ∀{a b} → (a ≤ b) ∨ (a > b)
      [≤]-or-[>] {a} {b} with converseTotal(_≤_){a}{b}
      [≤]-or-[>] {a} {b} | [∨]-introₗ ab = [∨]-introₗ ab
      [≤]-or-[>] {a} {b} | [∨]-introᵣ ba with [≡]-decidable {a}{b}
      [≤]-or-[>] {a} {b} | [∨]-introᵣ ba | [∨]-introₗ eqab  = [∨]-introₗ (subrelation(_≡_)(_≤_) eqab)
      [≤]-or-[>] {a} {b} | [∨]-introᵣ ba | [∨]-introᵣ neqab = [∨]-introᵣ (ab ↦ neqab(antisymmetry(_≤_)(_≡_) ab ba))

      [≤]-decidable : ∀{a b} → (a ≤ b) ∨ (a ≰ b)
      [≤]-decidable = [≤]-or-[>]

      [≥]-or-[<] : ∀{a b} → (a ≥ b) ∨ (a < b)
      [≥]-or-[<] = [≤]-or-[>]

      [≥]-decidable : ∀{a b} → (a ≥ b) ∨ (a ≱ b)
      [≥]-decidable = [≥]-or-[<]

      -- [<]-decidable : ∀{a b} → (a < b) ∨ (a ≮ b)
      -- [<]-decidable = [≥]-or-[<]

  excluded-middle-double : ∀{ℓ}§{P : Stmt{ℓ}} → ((¬ P) ∨ (¬¬ P))
  excluded-middle-double ([∨]-introₗ p)  (nnp) = p
  excluded-middle-double ([∨]-introᵣ np) (nnp) = [⊥]-elim(nnp(np))
