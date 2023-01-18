module Miscellaneous.TestLogic where

import      Lvl
open import Logic.Propositional
open import Type

private variable ℓ : Lvl.Level
private variable P Q R : Type{ℓ}

elimOr : (P → R) → (Q → R) → ¬((¬ P) ∧ (¬ Q)) → R
elimOr pr qr nnpnq = [⊥]-elim(nnpnq ([∧]-intro {!!} {!!}))
