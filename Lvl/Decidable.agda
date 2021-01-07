module Lvl.Decidable where

open import Data.Boolean.Stmt
open import Logic.Propositional
open import Logic.Propositional.Theorems
import      Lvl
open import Type.Properties.Decidable
open import Type.Properties.Decidable.Proofs
open import Type

private variable ℓ ℓ₁ : Lvl.Level

-- Changing classical propositions' universe levels by using their boolean representation.
module _ (P : Type{ℓ}) ⦃ dec : Decidable(0)(P) ⦄ where
  Convert : Type{ℓ₁}
  Convert = Lvl.Up(IsTrue(decide(0)(P)))

  -- LvlConvert is satisfied whenever its proposition is.
  Convert-correctness : P ↔ Convert{ℓ₁}
  Convert-correctness = [↔]-transitivity decider-true ([↔]-intro Lvl.Up.obj Lvl.up)
