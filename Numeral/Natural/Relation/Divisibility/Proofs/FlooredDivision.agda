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
divides-with-[⌊/⌋] {a}{b}{d} ⦃ pos-d ⦄ da db ba = divides-without-[⋅]ᵣ-both' {b ⌊/⌋ d}{a ⌊/⌋ d}{d}
  ([↔]-to-[→] Positive-greater-than-zero pos-d)
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

-- TODO: Move below

open import Lang.Instance
open import Logic.Propositional.Theorems
open import Numeral.Natural.Oper.Proofs.Multiplication
open import Structure.Operator

⌊/⌋[⋅]-almost-associativity : ∀{x y z} ⦃ pos-y : Positive(y) ⦄ ⦃ pos-z : Positive(z) ⦄ → (y ⋅ z ∣ x) → ((x ⌊/⌋ y) ⌊/⌋ z ≡ (x ⌊/⌋ (y ⋅ z)) ⦃ [⋅]-positive pos-y pos-z ⦄)
⌊/⌋[⋅]-almost-associativity {x}{y}{z} ⦃ pos-y ⦄ ⦃ pos-z ⦄ div = [⋅]-cancellationᵣ {x = y ⋅ z} $
  ((x ⌊/⌋ y) ⌊/⌋ z) ⋅ (y ⋅ z) 🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_)((x ⌊/⌋ y) ⌊/⌋ z) (commutativity(_⋅_) {y}{z}) ]
  ((x ⌊/⌋ y) ⌊/⌋ z) ⋅ (z ⋅ y) 🝖[ _≡_ ]-[ associativity(_⋅_) {(x ⌊/⌋ y) ⌊/⌋ z}{z}{y} ]-sym
  (((x ⌊/⌋ y) ⌊/⌋ z) ⋅ z) ⋅ y 🝖[ _≡_ ]-[ congruence₂ₗ(_⋅_)(y) ([⋅][⌊/⌋]-inverseOperatorᵣ {x ⌊/⌋ y}{z} ([↔]-to-[←] (divides-div {x}{y}{z} div-yx) div)) ]
  (x ⌊/⌋ y) ⋅ y               🝖[ _≡_ ]-[ [⋅][⌊/⌋]-inverseOperatorᵣ {x}{y} div-yx ]
  x                           🝖[ _≡_ ]-[ [⋅][⌊/⌋]-inverseOperatorᵣ {x}{y ⋅ z} div ]-sym
  (x ⌊/⌋ (y ⋅ z)) ⋅ (y ⋅ z)   🝖-end
  where
    instance
      pos-yz : Positive(y ⋅ z)
      pos-yz = [⋅]-positive pos-y pos-z

    div-yx : (y ∣ x)
    div-yx = [∧]-elimₗ (divides-of-[⋅]ₗ ([∧]-to-[↔] ([∧]-intro pos-y pos-z)) div)
