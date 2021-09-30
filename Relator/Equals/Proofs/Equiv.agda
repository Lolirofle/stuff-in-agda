open import Type

module Relator.Equals.Proofs.Equiv {ℓ} {T : Type{ℓ}} where

import Relator.Equals.Proofs.Equivalence

open Relator.Equals.Proofs.Equivalence.One   {T = T} public
open Relator.Equals.Proofs.Equivalence.Two   {A = T} public
open Relator.Equals.Proofs.Equivalence.Three {A = T} public
open Relator.Equals.Proofs.Equivalence.Four  {A = T} public

instance [≡]-unaryRelator-instance    = [≡]-unaryRelator
instance [≡]-binaryRelator-instance   = [≡]-binaryRelator
instance [≡]-binaryOperator-instance  = [≡]-binaryOperator
instance [≡]-trinaryOperator-instance = [≡]-trinaryOperator
instance [≡]-to-function-instance      = [≡]-to-function
instance [≡]-equiv-instance            = [≡]-equiv
