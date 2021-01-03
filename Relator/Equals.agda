module Relator.Equals where

import      Lvl
open import Logic
open import Logic.Propositional
open import Type

infixl 15 _≢_

open import Type.Identity public
  using()
  renaming(Id to infixl 15 _≡_ ; intro to [≡]-intro)

_≢_ : ∀{ℓ}{T} → T → T → Stmt{ℓ}
a ≢ b = ¬(a ≡ b)
