module Numeral.Natural.Oper.Modulo.Unclosed where

open import Data
open import Data.Option as Option using (Option)
open import Logic.Propositional
import      Lvl
open import Numeral.Finite as 𝕟 using (𝕟 ; ℕ-to-𝕟)
open import Numeral.Natural
import      Numeral.Natural.Oper.Modulo as ℕ
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order.Decidable
open import Type.Properties.Decidable.Proofs

-- Modulo operation resulting in an finite natural number.
_mod_ : ℕ → (b : ℕ) → ⦃ pos : Positive(b) ⦄ → 𝕟(b)
a mod b = ℕ-to-𝕟 (a ℕ.mod b) ⦃ [↔]-to-[→] decider-true (mod-maxᵣ{a}{b}) ⦄

_modₒₚₜ_ : ℕ → (b : ℕ) → Option(𝕟(b))
a modₒₚₜ 𝟎       = Option.None
a modₒₚₜ b@(𝐒 _) = Option.Some(a mod b)
