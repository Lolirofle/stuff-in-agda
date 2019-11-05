module Numeral.Natural.Oper.DivMod.Proofs where

import Lvl
open import Data
open import Data.Boolean.Stmt
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Relation.Order
open import Relator.Equals
open import Syntax.Function
open import Syntax.Transitivity
open import Type

postulate division-remainder : ∀{a b} → ⦃ _ : (a ≥ b) ⦄ → ⦃ _ : IsTrue(b ≢? 𝟎) ⦄ → ((b ⋅ (a ⌊/⌋ b)) + (a mod b) ≡ a)
-- division-remainder {.(𝐒 a)} {𝐒 𝟎}     ⦃ [≤]-with-[𝐒] {.0}     {a} ⦄ = {!!}
-- division-remainder {.(𝐒 a)} {𝐒 (𝐒 b)} ⦃ [≤]-with-[𝐒] {.(𝐒 b)} {a} ⦄ = {!!}
{-  ((a ⌊/⌋ b) ⋅ b) + (a mod b)
  a
-}
