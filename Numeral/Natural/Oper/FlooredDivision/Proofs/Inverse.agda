module Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse where

import Lvl
open import Data
open import Functional
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.DivMod.Proofs
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Multiplication
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Order
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity

[⋅][⌊/⌋]-inverseOperatorᵣ : ∀{x y} ⦃ pos : Positive(y) ⦄ → (y ∣ x) → (x ⌊/⌋ y ⋅ y ≡ x)
[⋅][⌊/⌋]-inverseOperatorᵣ {x}{𝐒 y} div =
  x ⌊/⌋ 𝐒(y) ⋅ 𝐒(y)                  🝖[ _≡_ ]-[]
  x ⌊/⌋ 𝐒(y) ⋅ 𝐒(y) + 𝟎              🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(_) ([↔]-to-[←] mod-divisibility div) ]-sym
  (x ⌊/⌋ 𝐒(y) ⋅ 𝐒(y)) + (x mod 𝐒(y)) 🝖[ _≡_ ]-[ [⌊/⌋][mod]-is-division-with-remainder {x}{y} ]
  x                                  🝖-end

[⌊/⌋][⋅]-inverseOperatorᵣ : ∀{x y} ⦃ pos : Positive(y) ⦄ → ((x ⋅ y) ⌊/⌋ y ≡ x)
[⌊/⌋][⋅]-inverseOperatorᵣ {x}{𝐒 y} = [⋅]-cancellationᵣ {𝐒(y)} ([⋅][⌊/⌋]-inverseOperatorᵣ (divides-with-[⋅] {𝐒(y)}{x} ([∨]-introᵣ (reflexivity(_∣_)))))

[⌊/⌋][swap⋅]-inverseOperatorᵣ : ∀{x y} ⦃ pos : Positive(x) ⦄ → ((x ⋅ y) ⌊/⌋ x ≡ y)
[⌊/⌋][swap⋅]-inverseOperatorᵣ {x}{y} = congruence₁(_⌊/⌋ x) (commutativity(_⋅_) {x}{y}) 🝖 [⌊/⌋][⋅]-inverseOperatorᵣ {y}{x}

[⋅][⌊/⌋₀]-inverseOperatorᵣ : ∀{x y} → (y > 0) → (y ∣ x) → ((x ⌊/⌋₀ y) ⋅ y ≡ x)
[⋅][⌊/⌋₀]-inverseOperatorᵣ {x}{𝐒 y} _ = [⋅][⌊/⌋]-inverseOperatorᵣ {x}{𝐒 y}
