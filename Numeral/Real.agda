module Numeral.Real where

import Level as Lvl
open import Functional
open import Logic.Propositional{Lvl.𝟎}
open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
open import Numeral.Integer hiding (𝟎 ; −_ ; abs)
open import Numeral.Natural
open import Structure.Operator.Field{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Operator.Group{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Operator.Properties{Lvl.𝟎}{Lvl.𝟎}

-- TODO: Write it properly (maybe with a "construction of the reals"?). The following in this file is something to get this started

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [The set]
postulate ℝ : Set

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Conversions]
record [ℝ]-conversion (T : Set) : Set where
  infixl 10000 #_
  field
    #_ : T → ℝ
open [ℝ]-conversion {{...}} public

instance postulate [ℕ]-to-[ℝ] : [ℝ]-conversion(ℕ)
instance postulate [ℤ]-to-[ℝ] : [ℝ]-conversion(ℤ)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Elements]
postulate e : ℝ
postulate π : ℝ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Operators]
postulate _+_ : ℝ → ℝ → ℝ
postulate _−_ : ℝ → ℝ → ℝ
postulate _⋅_ : ℝ → ℝ → ℝ
postulate _/_ : ℝ → ℝ → ℝ
postulate _^_ : ℝ → ℝ → ℝ
postulate log : ℝ → ℝ → ℝ
postulate _√_ : ℝ → ℝ → ℝ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Functions]
postulate abs : ℝ → ℝ
postulate sin : ℝ → ℝ
postulate cos : ℝ → ℝ
postulate tan : ℝ → ℝ
postulate asin : ℝ → ℝ
postulate acos : ℝ → ℝ
postulate atan : ℝ → ℝ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Relations]

-- Equals
postulate _≡_ : ℝ → ℝ → Stmt

-- Lesser than
postulate _<_ : ℝ → ℝ → Stmt

-- Not equals
_≢_ : ℝ → ℝ → Stmt
x ≢ y = ¬(x ≡ y)

-- Greater than
_>_ : ℝ → ℝ → Stmt
x > y = y < x

-- Lesser than or equals
_≤_ : ℝ → ℝ → Stmt
x ≤ y = (x < y) ∨ (x ≡ y)

-- Greater than or equals
_≥_ : ℝ → ℝ → Stmt
x ≥ y = (x > y) ∨ (x ≡ y)

-- In an interval
_<_<_ : ℝ → ℝ → ℝ → Stmt
x < y < z = (x < y) ∧ (y < z)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Properties of operations on ℝ]
instance
  [ℝ]-fieldSym : FieldSym
  [ℝ]-fieldSym =
    record{
      _+_     = _+_ ;
      _⋅_     = _⋅_ ;
      [+]-id  = #(0) ;
      [+]-inv = #(0) −_ ;
      [⋅]-id  = #(1) ;
      [⋅]-inv = #(1) /_
    }

instance
  postulate [ℝ]-field : Field {ℝ}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Data structures]

-- Positive real numbers
data ℝ₊ : Set where
  r₊ : (x : ℝ) → (x > #(0)) → ℝ₊

instance
  [ℝ₊]-to-[ℝ] : [ℝ]-conversion(ℝ₊)
  [ℝ₊]-to-[ℝ] = record{#_ = f} where
    f : ℝ₊ → ℝ
    f(r₊ x _) = x

data OpenInterval (a : ℝ) (b : ℝ) : Set where
  open-interval : (a ≤ b) → OpenInterval(a)(b)

data ClosedInterval (a : ℝ) (b : ℝ) : Set where
  closed-interval : (a ≤ b) → ClosedInterval(a)(b)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Properties on functions of ℝ]

module Limit where
  Limit : (ℝ → ℝ) → ℝ → ℝ → Stmt
  Limit f(l) L = ∀{ε : ℝ₊} → ∃{ℝ₊}(δ ↦ ∀{x : ℝ} → (#(0) < abs(x − l) < #(δ)) → (abs(f(x) − L) < #(ε)))

  lim : (f : ℝ → ℝ) → (x : ℝ) → ∀{L} → {{_ : Limit f(x) (L)}} → ℝ
  lim _ _ {L} = L

module Continuity where
  open Limit

  ContinuousPoint : (ℝ → ℝ) → ℝ → Stmt
  ContinuousPoint f(x) = Limit f(x) (f(x))

  Continuous : (ℝ → ℝ) → Stmt
  Continuous f = ∀{x} → ContinuousPoint f(x)

module Derivative where
  open Limit

  Derivative : (ℝ → ℝ) → ℝ → ℝ → Stmt
  Derivative f(p) D = Limit(x ↦ ((f(x) − f(p))/(x − p)))(# 0)(D)

  𝐷 : (f : ℝ → ℝ) → (x : ℝ) → ∀{D} → {{_ : Derivative f(x) D}} → ℝ
  𝐷 _ _ {D} = D

  -- DifferentiablePoint : (ℝ → ℝ) → ℝ → Stmt

-- postulate Axiom1 : {x y : ℝ} → (x < y) → ¬ (y < x)
-- postulate Axiom2 : {x z : ℝ} → (x < z) → ∃(y ↦ (x < y) ∧ (y < z))
-- postulate Axiom4 : {x y z : ℝ} → ((x + y) + z) ≡ (x + (y + z))
-- postulate Axiom5 : {x y : ℝ} → ∃(z ↦ (x + z) ≡ y)
