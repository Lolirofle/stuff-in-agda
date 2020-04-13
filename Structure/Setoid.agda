module Structure.Setoid where -- TODO: Move to Structure.Setoid

open import Structure.Setoid.WithLvl hiding (Equiv ; module Equiv ; Setoid ; module Setoid ; module EquivInnerModule ; _≡_ ; _≢_ ; [≡]-equivalence) public
open import Type

module _ {ℓₒ} where
  open Structure.Setoid.WithLvl.EquivInnerModule{ℓₒ}{ℓₒ} public
