module Formalization.LambdaCalculus.ByVarCount.ByIndices.Semantics.CallByName where

import      Lvl
open import Data
open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.Semantics
open import Formalization.LambdaCalculus.ByVarCount.Functions
open import Logic.Predicate
open import Numeral.Finite
open import Numeral.Natural
open import Syntax.Number
open import Type

private variable d db : ℕ
private variable f t x : Term(d)
private variable body : Term(db)
private variable v : ∃(Value)

data _⇓_ : Term(d) → ∃(Value) → Type{0} where
  value : ⦃ val : Value(t) ⦄ → (t ⇓ [∃]-intro t)
  apply : (f ⇓ [∃]-intro(Abstract body)) → (substituteVar 0 x body ⇓ v) → (Apply f x ⇓ v)
