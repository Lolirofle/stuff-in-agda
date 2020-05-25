module Lang.Irrelevance where

open import Type

postulate .axiom : ∀{ℓ}{T : Type{ℓ}} -> .T -> T
