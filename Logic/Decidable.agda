open import Data.Tuple.Raise
open import Numeral.Natural
open import Type

module Logic.Decidable {ℓ} {n : ℕ} {As : Type{ℓ} ^ n} where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Proofs using (module IsTrue ; module IsFalse)
open import Data.Boolean.Proofs
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Function.Multi
open import Lang.Instance
open import Logic
open import Logic.Names
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Logic.Predicate.Theorems
open import Relator.Equals
open import Type
open import Type.Empty

record Decidable (P : As ⇉ Stmt{ℓ}) : Stmt where
  constructor intro
  field
    decide : Bool
