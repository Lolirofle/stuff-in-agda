module Formalization.LambdaCalculus.Semantics.CallByValue where

import      Lvl
open import Data
open import Formalization.LambdaCalculus
open import Formalization.LambdaCalculus.Semantics
open import Formalization.LambdaCalculus.SyntaxTransformation
open import Logic.Predicate
open import Numeral.Natural
open import Syntax.Number
open import Type

private variable d db : ℕ
private variable f t x : Term(d)
private variable body : Term(db)
private variable v vx : ∃(Value)

data _⇓_ : Term(d) → ∃(Value) → Type{0} where
  value : ⦃ val : Value(t) ⦄ → (t ⇓ [∃]-intro t)
  apply : (f ⇓ [∃]-intro(Abstract body)) → (x ⇓ vx) → (substituteVar0 ([∃]-witness vx) body ⇓ v) → (Apply f x ⇓ v)
