module Numeral.Finite.Equiv where

open import Numeral.Finite
open import Relator.Equals.Proofs.Equiv
open import Structure.Setoid

instance
  𝕟-equiv : ∀{n} → Equiv(𝕟(n))
  𝕟-equiv = [≡]-equiv
