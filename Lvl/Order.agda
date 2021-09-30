module Lvl.Order where

import      Lvl
open import Relator.Equals.Proofs.Equiv
import      Structure.Operator.Lattice.OrderRelation
open import Type

_≤_ : Lvl.Level → Lvl.Level → Type
_≤_ = Structure.Operator.Lattice.OrderRelation.order(Lvl.Level)(Lvl._⊔_)
