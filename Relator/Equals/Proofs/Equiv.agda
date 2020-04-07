open import Type

module Relator.Equals.Proofs.Equiv {ℓ} (T : Type{ℓ}) where

open import Relator.Equals.Proofs.Equivalence

open Relator.Equals.Proofs.Equivalence.One {T = T} public
open Relator.Equals.Proofs.Equivalence.Two {A = T} using ([≡]-to-function) public
