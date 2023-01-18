module Numeral.Natural.UnclosedOper where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Boolean.Stmt
open import Data.Option as Option using (Option)
open import Data.Option.Functions as Option
open import Logic.Propositional
open import Numeral.Finite as 𝕟 using (𝕟 ; 𝕟₌ ; fromℕ)
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
import      Numeral.Natural.Oper.Modulo as ℕ
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Relation.Order.Decidable
open import Type.Properties.Decidable.Proofs

infix  10010 _−_

-- Total subtraction from natural numbers to an optional natural number.
-- When the subtraction gives a negative number semantically (when a < b), this operation gives Option.None.
_−?_ : ℕ → ℕ → Option(ℕ)
a    −? 𝟎    = Option.Some(a)
𝟎    −? 𝐒(b) = Option.None
𝐒(a) −? 𝐒(b) = a −? b

{-# TERMINATING #-}
divmod? : ℕ → ℕ → Option(ℕ ⨯ ℕ)
divmod? x       𝟎       = Option.None
divmod? 𝟎       (𝐒 _)   = Option.Some(𝟎 , 𝟎)
divmod? x@(𝐒 _) y@(𝐒 _) with (x −? y)
... | Option.Some(d) = Option.map (Tuple.mapLeft 𝐒) (divmod? d y)
... | Option.None    = Option.Some(𝟎 , x)

-- Subtracting a finite natural number.
_−_ : (x : ℕ) → 𝕟₌(x) → ℕ
x    − 𝕟.𝟎    = x
𝐒(x) − 𝕟.𝐒(y) = x − y
