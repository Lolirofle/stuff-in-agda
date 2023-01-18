module Numeral.Natural.Relation.ModuloCongruence.Equiv where

open import Numeral.Natural
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.ModuloCongruence
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator.Equivalence
open import Structure.Relator.Equivalence.Proofs.On₂
open import Structure.Setoid using (Equiv ; intro)

private variable m : ℕ

instance
  mod-congruence-equivalence : ⦃ pos : Positive(m) ⦄ → Equivalence(_≡_[mod m ])
  mod-congruence-equivalence {m} = on₂-equivalence {f = _mod m} ⦃ [≡]-equivalence ⦄

mod-congruence-equiv : (m : ℕ) → ⦃ pos : Positive(m) ⦄ → Equiv(ℕ)
mod-congruence-equiv m = intro(_≡_[mod m ]) ⦃ mod-congruence-equivalence {m} ⦄
