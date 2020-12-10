module Structure.Real where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Proofs
import      Data.Either as Either
open import Functional
open import Logic
open import Logic.Classical
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural using (ℕ)
import      Numeral.Natural.Relation.Order as ℕ
open import Relator.Ordering
open import Structure.Setoid
open import Structure.Function.Ordering
open import Structure.Operator.Field
open import Structure.Operator.Monoid
open import Structure.Operator.Group
open import Structure.Operator.Proofs
open import Structure.Operator.Properties
open import Structure.Relator.Ordering
open        Structure.Relator.Ordering.Weak.Properties
open import Structure.Relator.Properties
open import Structure.OrderedField
import      Structure.OrderedField.AbsoluteValue
open import Syntax.Transitivity
open import Type

-- Theory defining the axioms of ℝ in classical logic.
-- The axioms are the following:
-- • An ordered field.
-- • Monotone convergence.
record RealTheory {ℓ₁ ℓ₂} {R : Type{ℓ₁}} ⦃ _ : Equiv(R) ⦄ (_+_ _⋅_ : R → R → R) (_≤_ : R → R → Stmt{ℓ₂}) ⦃ classical : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P) ⦄ : Type{ℓ₁ Lvl.⊔ Lvl.𝐒(ℓ₂)} where
  field
    ⦃ orderedField ⦄ : OrderedField(_+_)(_⋅_)(_≤_)

  open OrderedField(orderedField) public
  open Structure.OrderedField.AbsoluteValue(_+_)(_⋅_)(_≤_)

  field
    sup-fn : (f : ℕ → R) → ⦃ Increasing(ℕ._≤_)(_≤_)(f) ⦄ → ⦃ UpperBounded(ℕ._≤_)(_≤_)(f) ⦄ → R
    monotone-convergence : ∀{f} → ⦃ inc : Increasing(ℕ._≤_)(_≤_)(f) ⦄ → ⦃ bound : UpperBounded(ℕ._≤_)(_≤_)(f) ⦄ → ∃{Obj = R → ℕ}(N ↦ ∀{ε} → (ε > 𝟎) → ∀{n} → (n ℕ.> N(ε)) → (‖ f(n) − sup-fn (f) ⦃ inc ⦄ ⦃ bound ⦄ ‖ < ε))

  -- TODO: Consider adding something that relates addition and multiplication so that it conform to the axioms of arithmetic and their definitions of addition and multiplication. This is so that one should be able to prove (x + x ≡ 𝐒(𝐒(𝟎)) ⋅ x) or (2.5 ⋅ x = x + x + x/2) (when 𝐒, the successor function is defined as (1 +_)) for easier to write statements. In other words: add ((1 + x) ⋅ y = x + (x ⋅ y)) as an axiom. (20201210 Is this TODO outdated?)
