open import Type

module Relator.Equals.Proofs.Equiv {ℓ} {T : Type{ℓ}} where

import Relator.Equals.Proofs.Equivalence

open Relator.Equals.Proofs.Equivalence.One   {T = T} public
open Relator.Equals.Proofs.Equivalence.Two   {A = T} public
open Relator.Equals.Proofs.Equivalence.Three {A = T} public
open Relator.Equals.Proofs.Equivalence.Four  {A = T} public

instance [≡]-unary-relator-instance    = [≡]-unary-relator
instance [≡]-binary-relator-instance   = [≡]-binary-relator
instance [≡]-binary-operator-instance  = [≡]-binary-operator
instance [≡]-trinary-operator-instance = [≡]-trinary-operator
instance [≡]-to-function-instance      = [≡]-to-function
instance [≡]-equiv-instance            = [≡]-equiv
