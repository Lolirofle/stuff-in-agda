module Formalization.ClassicalPropositionalLogic.Syntax.Proofs where

import      Lvl
open import Formalization.ClassicalPropositionalLogic.Syntax
open import Relator.Equals.Proofs.Equiv
open import Type.Size.Countable
open import Type

private variable ℓₚ ℓ : Lvl.Level
private variable P : Type{ℓₚ}

-- TODO: How would a proof of this look like?
instance
  postulate Formula-is-countably-infinite : ⦃ _ : CountablyInfinite(P) ⦄ → CountablyInfinite(Formula(P))

{-
open import Type.W
Formula-W-bijectivity : Bijective(W{A = 𝕟(8)}())
Formula-W-bijectivity = {!!
-}
