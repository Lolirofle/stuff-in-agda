module Numeral.Natural.Relation.Divisibility.Proofs.FlooredDivision where

import Lvl
open import Data
open import Functional
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Proofs
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Structure.Operator.Properties
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv

divides-with-[⌊/⌋] : ∀{a b d} ⦃ pos-d : Positive(d) ⦄ → (d ∣ a) → (d ∣ b) → (b ∣ a) → ((b ⌊/⌋ d) ∣ (a ⌊/⌋ d))
divides-with-[⌊/⌋] {a}{b}{d} da db ba = divides-without-[⋅]ᵣ-both' {b ⌊/⌋ d}{a ⌊/⌋ d}{d}
  (substitute₂(_∣_)
    (symmetry(_≡_) ([⋅][⌊/⌋]-inverseOperatorᵣ db))
    (symmetry(_≡_) ([⋅][⌊/⌋]-inverseOperatorᵣ da))
    ba
  )

divides-div : ∀{a b c} ⦃ pos-b : Positive(b) ⦄ ⦃ pos-c : Positive(c) ⦄ → (b ∣ a) → ((c ∣ (a ⌊/⌋ b)) ↔ ((b ⋅ c) ∣ a))
divides-div {a}{b}{c} ba = [↔]-intro l r where
  l : ((c ∣ (a ⌊/⌋ b)) ← ((b ⋅ c) ∣ a))
  l bca = substitute₂ₗ(_∣_) ([⌊/⌋][swap⋅]-inverseOperatorᵣ {b}{c}) (divides-with-[⌊/⌋] {a}{b ⋅ c}{b} ba (divides-with-[⋅] {b}{b}{c} ([∨]-introₗ (reflexivity(_∣_)))) bca)

  r : ((c ∣ (a ⌊/⌋ b)) → ((b ⋅ c) ∣ a))
  r cab = substitute₂ᵣ(_∣_) (commutativity(_⋅_) {b}{a ⌊/⌋ b} 🝖 [⋅][⌊/⌋]-inverseOperatorᵣ {a}{b} ba) (divides-with-[⋅]ₗ-both {c}{a ⌊/⌋ b}{b} cab)

divides-without-divᵣ : ∀{a b c} ⦃ pos-b : Positive(b) ⦄ → (b ∣ a) → (c ∣ (a ⌊/⌋ b)) → (c ∣ a)
divides-without-divᵣ{a}{b}{c} ba cab = substitute₂ᵣ(_∣_) ([⋅][⌊/⌋]-inverseOperatorᵣ ba) (divides-with-[⋅] {c = b} ([∨]-introₗ cab))
