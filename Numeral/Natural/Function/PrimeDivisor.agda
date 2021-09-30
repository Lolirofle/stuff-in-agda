module Numeral.Natural.Function.PrimeDivisor where

open import Data
open import Data.List
open import Functional
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Function.Divisor
open import Numeral.Natural.Function.Divisor.Proofs
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Decidable
open import Structure.Relator.Ordering
open import Type.Properties.Decidable.Proofs

primeDivisorsRec : (n : ℕ) → ((i : ℕ) → ⦃ i < n ⦄ → List(ℕ)) → List(ℕ)
primeDivisorsRec 0          prev = ∅
primeDivisorsRec 1          prev = ∅
primeDivisorsRec n@(𝐒(𝐒 _)) prev =
  let d = leastDivisor n
  in (d ⊰ prev ((n ⌊/⌋ d) ⦃ [↔]-to-[→] decider-true (leastDivisor-positive{n} <>) ⦄) ⦃ [⌊/⌋]-ltₗ {n}{leastDivisor n} ⦃ [↔]-to-[→] decider-true (leastDivisor-range{n} (succ(succ min))) ⦄ ⦄)
primeDivisors : ℕ → List(ℕ)
primeDivisors = Strict.Properties.wellfounded-recursion(_<_) {P = const(List(ℕ))} primeDivisorsRec
