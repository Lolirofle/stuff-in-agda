module Numeral.Real where

import Lvl
open import Syntax.Number
open import Data
open import Functional
open import Logic.Propositional{Lvl.𝟎}
open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
open import Numeral.Integer hiding (𝟎)
open import Numeral.Natural
open import Sets.PredicateSet.Filter{Lvl.𝟎}{Lvl.𝟎}
open import Sets.Setoid{Lvl.𝟎}
open import Structure.Operator.Field{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Operator.Group{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Operator.Properties{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Real{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Relator.Ordering{Lvl.𝟎}{Lvl.𝟎}

-- TODO: Write it properly (maybe with a "construction of the reals"?). The following in this file is something to get this started

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [The set]

postulate ℝ : Set

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Relations]

-- infixr 100 _≡_ _≢_ _<_ _>_ _≤_ _≥_ _<_<_

-- Equals
instance postulate [≡]-equiv : Equiv(ℝ)

-- Lesser than
postulate _<_ : ℝ → ℝ → Stmt

open From-[<][≡] (_<_) (_≡_) public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Conversions]

record [ℝ]-conversion (T : Set) : Set where
  infixl 10000 #_
  field
    #_ : T → ℝ
open [ℝ]-conversion ⦃ ... ⦄ public

instance postulate [ℤ]-to-[ℝ] : [ℝ]-conversion(ℤ)
instance postulate [ℕ]-to-[ℝ] : [ℝ]-conversion(ℕ)

instance
  postulate ℝ-InfiniteNumeral : InfiniteNumeral (ℝ)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Subsets]

instance
  subset-to-[ℝ] : ∀{P} → [ℝ]-conversion(Filter{ℝ}(P))
  subset-to-[ℝ] {P} = record{#_ = f} where
    f : Filter{ℝ}(P) → ℝ
    f(subelem x) = x

-- Positive real numbers
ℝ₊ = Filter{ℝ}(x ↦ (x > 0))

-- Negative real numbers
ℝ₋ = Filter{ℝ}(x ↦ (x < 0))

-- Non-zero real numbers
ℝ₊₋ = Filter{ℝ}(x ↦ (x ≢ 0))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Elements]

postulate e : ℝ
postulate π : ℝ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Operators]

infixl 1000 _+_ _−_
infixl 1001 _⋅_ _/_
infixl 1002 _^_ _√_
postulate _+_ : ℝ → ℝ → ℝ
postulate _−_ : ℝ → ℝ → ℝ
postulate _⋅_ : ℝ → ℝ → ℝ
postulate _/_ : ℝ → ℝ → ℝ -- TODO: Some of these are partial functions/have smaller domains
postulate _^_ : ℝ → ℝ → ℝ
postulate log : ℝ → ℝ → ℝ
postulate _√_ : ℝ → ℝ → ℝ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Functions]

abs : ℝ → ℝ
abs(x) = 2 √ (x ^ 2)

postulate sin : ℝ → ℝ

cos : ℝ → ℝ
cos(x) = sin(x − (π / 2))

tan : ℝ → ℝ
tan(x) = sin(x) / cos(x)

postulate asin : ℝ → ℝ
postulate acos : ℝ → ℝ
postulate atan : ℝ → ℝ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Stuctures]

instance
  postulate [ℝ]-realTheory : RealTheory(_+_)(_⋅_)(_≤_)

instance
  postulate [ℝ][<]-strictPartialOrder : Strict.Order {ℝ} (_<_)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Properties of functions in ℝ]

instance postulate abs-positive : ∀{x} → (abs(x) ≥ 0)
instance postulate cos-periodicity : ∀{v}{n : ℕ} → (cos(v) ≡ cos(v + 2 ⋅ π ⋅ #(n)))
instance postulate sin-periodicity : ∀{v}{n : ℕ} → (sin(v) ≡ sin(v + 2 ⋅ π ⋅ #(n)))
instance postulate cos-even : ∀{v} → (cos(v) ≡ cos(0 − v))
instance postulate sin-odd  : ∀{v} → (sin(v) ≡ 0 − sin(0 − v))
instance postulate circle : ∀{v} → (cos(v) ^ 2 + sin(v) ^ 2 ≡ 1)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Properties on functions of ℝ]





-- postulate Axiom1 : {x y : ℝ} → (x < y) → ¬ (y < x)
-- postulate Axiom2 : {x z : ℝ} → (x < z) → ∃(y ↦ (x < y) ∧ (y < z))
-- postulate Axiom4 : {x y z : ℝ} → ((x + y) + z) ≡ (x + (y + z))
-- postulate Axiom5 : {x y : ℝ} → ∃(z ↦ (x + z) ≡ y)
