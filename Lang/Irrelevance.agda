module Lang.Irrelevance where

import      Lvl
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

-- In the irrelevant universe, an irrelevant object can be made into a relevant object (but it is still irrelevant).
postulate .idᵢᵣᵣ : .T → T
