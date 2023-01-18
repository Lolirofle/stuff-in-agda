module Numeral.Natural.Oper.DivMod.Proofs where

import Lvl
open import Data
open import Data.Boolean.Stmt
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs.DivisibilityWithRemainder
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Modulo.Proofs.DivisibilityWithRemainder
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.DivisibilityWithRemainder
open import Numeral.Natural.Relation.DivisibilityWithRemainder.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Existence using ([≤]-equivalence)
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Operator
open import Structure.Operator.Proofs.Util
open import Structure.Operator.Properties
open import Syntax.Transitivity

-- The division theorem.
[⌊/⌋][mod]-is-division-with-remainder : ∀{x y} ⦃ pos : Positive(y) ⦄ → (((x ⌊/⌋ y) ⋅ y) + (x mod y) ≡ x)
[⌊/⌋][mod]-is-division-with-remainder {x}{y} with [∃]-intro r ⦃ p ⦄ ← [∣ᵣₑₘ]-existence-alt {x}{y} =
  ((x ⌊/⌋ y) ⋅ y) + (x mod y)                               🝖[ _≡_ ]-[ congruence₂(_+_) (congruence₂-₁(_⋅_)(y) ([⌊/⌋][∣ᵣₑₘ]-quotient-equality {x}{y}{r}{p})) ([mod][∣ᵣₑₘ]-remainder-equality {x}{y}{r}{p}) ]
  (([∣ᵣₑₘ]-quotient p) ⋅ y) + (toℕ ([∣ᵣₑₘ]-remainder p)) 🝖[ _≡_ ]-[ [∣ᵣₑₘ]-is-division-with-remainder {x}{y}{r} p ]
  x                                                         🝖-end

[⌊/⌋][mod]-is-division-with-remainder-pred-commuted : ∀{x y} ⦃ pos : Positive(y) ⦄ → ((y ⋅ (x ⌊/⌋ y)) + (x mod y) ≡ x)
[⌊/⌋][mod]-is-division-with-remainder-pred-commuted {x}{y} = congruence₁(_+ (x mod y)) (commutativity(_⋅_) {y}{x ⌊/⌋ y}) 🝖 [⌊/⌋][mod]-is-division-with-remainder {x}{y}

-- Floored division and multiplication is not inverse operators for all numbers.
-- This shows why it is not exactly.
[⌊/⌋][⋅]-semiInverseOperatorᵣ : ∀{a b} ⦃ pos : Positive(b) ⦄ → ((a ⌊/⌋ b) ⋅ b ≡ a −₀ (a mod b))
[⌊/⌋][⋅]-semiInverseOperatorᵣ {a}{b} =
  (a ⌊/⌋ b) ⋅ b 🝖[ _≡_ ]-[ OneTypeTwoOp.moveᵣ-to-invOp {b = a mod b}{c = a} (([⌊/⌋][mod]-is-division-with-remainder {y = b})) ]
  a −₀ (a mod b)   🝖-end

-- Floored division and multiplication is not inverse operators for all numbers.
-- This theorem shows that modulo is the error term (difference between the actual value for it to be inverse and value of the operation).
[⌊/⌋][⋅]-inverseOperatorᵣ-error : ∀{a b} ⦃ pos : Positive(b) ⦄ → (a mod b ≡ a −₀ (a ⌊/⌋ b ⋅ b))
[⌊/⌋][⋅]-inverseOperatorᵣ-error {a}{b} =
  (a mod b)             🝖[ _≡_ ]-[ OneTypeTwoOp.moveᵣ-to-invOp {a = a mod b}{b = (a ⌊/⌋ b) ⋅ b}{c = a} (commutativity(_+_) {a mod b}{(a ⌊/⌋ b) ⋅ b} 🝖 [⌊/⌋][mod]-is-division-with-remainder {y = b}) ]
  a −₀ (a ⌊/⌋ b ⋅ b) 🝖-end

[⌊/⌋][⋅]-semiInverse-order : ∀{x y} ⦃ pos : Positive(y) ⦄ → (((x ⌊/⌋ y) ⋅ y) ≤ x)
[⌊/⌋][⋅]-semiInverse-order {x}{y} = [↔]-to-[→] [≤]-equivalence ([∃]-intro (x mod y) ⦃ [⌊/⌋][mod]-is-division-with-remainder {x}{y} ⦄)
