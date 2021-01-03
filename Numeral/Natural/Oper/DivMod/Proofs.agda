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
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.DivisibilityWithRemainder
open import Numeral.Natural.Relation.DivisibilityWithRemainder.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Operator
open import Structure.Operator.Properties
open import Syntax.Transitivity

-- The division theorem.
[⌊/⌋][mod]-is-division-with-remainder : ∀{x y} → (((x ⌊/⌋ 𝐒(y)) ⋅ 𝐒(y)) + (x mod 𝐒(y)) ≡ x)
[⌊/⌋][mod]-is-division-with-remainder {x}{y} with [∃]-intro r ⦃ p ⦄ ← [∣ᵣₑₘ]-existence-alt {x}{y} =
  ((x ⌊/⌋ 𝐒(y)) ⋅ 𝐒(y)) + (x mod 𝐒(y))                         🝖[ _≡_ ]-[ congruence₂(_+_) (congruence₂ₗ(_⋅_)(𝐒(y)) ([⌊/⌋][∣ᵣₑₘ]-quotient-equality {x}{y}{r}{p})) ([mod][∣ᵣₑₘ]-remainder-equality {x}{y}{r}{p}) ]
  (([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)) + (𝕟-to-ℕ ([∣ᵣₑₘ]-remainder p)) 🝖[ _≡_ ]-[ [∣ᵣₑₘ]-is-division-with-remainder {x}{𝐒(y)}{r} p ]
  x                                                            🝖-end

[⌊/⌋][mod]-is-division-with-remainder-pred-commuted : ∀{x y} ⦃ _ : IsTrue(positive?(y)) ⦄ → ((y ⋅ (x ⌊/⌋ y)) + (x mod y) ≡ x)
[⌊/⌋][mod]-is-division-with-remainder-pred-commuted {x} {𝐒 y} = [≡]-with(_+ (x mod 𝐒(y))) (commutativity(_⋅_) {𝐒(y)}{x ⌊/⌋ 𝐒(y)}) 🝖 [⌊/⌋][mod]-is-division-with-remainder {x}{y}
