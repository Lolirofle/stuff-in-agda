module Numeral.Natural.Oper.DivMod.Proofs where

import Lvl
open import Data
open import Data.Boolean.Stmt
open import Logic.Predicate
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
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Operator
open import Structure.Operator.Proofs.Util
open import Structure.Operator.Properties
open import Syntax.Transitivity

-- The division theorem.
[⌊/⌋][mod]-is-division-with-remainder : ∀{x y} → (((x ⌊/⌋ 𝐒(y)) ⋅ 𝐒(y)) + (x mod 𝐒(y)) ≡ x)
[⌊/⌋][mod]-is-division-with-remainder {x}{y} with [∃]-intro r ⦃ p ⦄ ← [∣ᵣₑₘ]-existence-alt {x}{y} =
  ((x ⌊/⌋ 𝐒(y)) ⋅ 𝐒(y)) + (x mod 𝐒(y))                         🝖[ _≡_ ]-[ congruence₂(_+_) (congruence₂-₁(_⋅_)(𝐒(y)) ([⌊/⌋][∣ᵣₑₘ]-quotient-equality {x}{y}{r}{p})) ([mod][∣ᵣₑₘ]-remainder-equality {x}{y}{r}{p}) ]
  (([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)) + (𝕟-to-ℕ ([∣ᵣₑₘ]-remainder p)) 🝖[ _≡_ ]-[ [∣ᵣₑₘ]-is-division-with-remainder {x}{𝐒(y)}{r} p ]
  x                                                            🝖-end

[⌊/⌋][mod]-is-division-with-remainder-pred-commuted : ∀{x y} ⦃ _ : Positive(y) ⦄ → ((y ⋅ (x ⌊/⌋ y)) + (x mod y) ≡ x)
[⌊/⌋][mod]-is-division-with-remainder-pred-commuted {x} {𝐒 y} = congruence₁(_+ (x mod 𝐒(y))) (commutativity(_⋅_) {𝐒(y)}{x ⌊/⌋ 𝐒(y)}) 🝖 [⌊/⌋][mod]-is-division-with-remainder {x}{y}

-- Floored division and multiplication is not inverse operators for all numbers.
-- This shows why it is not exactly.
[⌊/⌋][⋅]-semiInverseOperatorᵣ : ∀{a b} → ((a ⌊/⌋ 𝐒(b)) ⋅ 𝐒(b) ≡ a −₀ (a mod 𝐒(b)))
[⌊/⌋][⋅]-semiInverseOperatorᵣ {a}{b} =
  (a ⌊/⌋ 𝐒(b)) ⋅ 𝐒(b) 🝖[ _≡_ ]-[ OneTypeTwoOp.moveᵣ-to-invOp {b = a mod 𝐒(b)}{c = a} (([⌊/⌋][mod]-is-division-with-remainder {y = b})) ]
  a −₀ (a mod 𝐒(b))   🝖-end

-- Floored division and multiplication is not inverse operators for all numbers.
-- This theorem shows that modulo is the error term (difference between the actual value for it to be inverse and value of the operation).
[⌊/⌋][⋅]-inverseOperatorᵣ-error : ∀{a b} → (a mod 𝐒(b) ≡ a −₀ (a ⌊/⌋ 𝐒(b) ⋅ 𝐒(b)))
[⌊/⌋][⋅]-inverseOperatorᵣ-error {a}{b} =
  (a mod 𝐒(b))             🝖[ _≡_ ]-[ OneTypeTwoOp.moveᵣ-to-invOp {a = a mod 𝐒(b)}{b = (a ⌊/⌋ 𝐒(b)) ⋅ 𝐒(b)}{c = a} (commutativity(_+_) {a mod 𝐒(b)}{(a ⌊/⌋ 𝐒(b)) ⋅ 𝐒(b)} 🝖 [⌊/⌋][mod]-is-division-with-remainder {y = b}) ]
  a −₀ (a ⌊/⌋ 𝐒(b) ⋅ 𝐒(b)) 🝖-end
