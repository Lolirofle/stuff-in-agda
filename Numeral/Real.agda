module Numeral.Real where

import Level as Lvl
open import Functional
open import Logic.Propositional{Lvl.𝟎}
open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
open import Numeral.Integer hiding (𝟎 ; −_)
open import Numeral.Natural
open import Structure.Operator.Field{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Operator.Group{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Operator.Properties{Lvl.𝟎}{Lvl.𝟎}

-- TODO: Write it properly. This is just to get started on something at all

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- The set
postulate ℝ : Set

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Conversions
postulate nat : ℕ → ℝ
postulate int : ℤ → ℝ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Elements
postulate e : ℝ
postulate π : ℝ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Operators
postulate _+_ : ℝ → ℝ → ℝ
postulate _−_ : ℝ → ℝ → ℝ
postulate _⋅_ : ℝ → ℝ → ℝ
postulate _/_ : ℝ → ℝ → ℝ
postulate _^_ : ℝ → ℝ → ℝ
postulate log : ℝ → ℝ → ℝ
postulate _√_ : ℝ → ℝ → ℝ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Functions
postulate sin : ℝ → ℝ
postulate cos : ℝ → ℝ
postulate tan : ℝ → ℝ
postulate asin : ℝ → ℝ
postulate acos : ℝ → ℝ
postulate atan : ℝ → ℝ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Relations
postulate _≡_ : ℝ → ℝ → Stmt
postulate _<_ : ℝ → ℝ → Stmt

_≢_ : ℝ → ℝ → Stmt
x ≢ y = ¬(x ≡ y)

_>_ : ℝ → ℝ → Stmt
x > y = y < x

_≤_ : ℝ → ℝ → Stmt
x ≤ y = (x < y) ∨ (x ≡ y)

_≥_ : ℝ → ℝ → Stmt
x ≥ y = (x > y) ∨ (x ≡ y)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Properties of ℝ and its relations and functions
instance
  [ℝ]-fieldSym : FieldSym
  [ℝ]-fieldSym =
    record{
      _+_     = _+_ ;
      _⋅_     = _⋅_ ;
      [+]-id  = nat(0) ;
      [+]-inv = nat(0) −_ ;
      [⋅]-id  = nat(1) ;
      [⋅]-inv = nat(1) /_
    }

instance
  postulate [ℝ]-field : Field {ℝ}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Data structures
ℝ₊ = ((x : ℝ) → (x > nat(0)))

data OpenInterval (a : ℝ) (b : ℝ) : Stmt where
  open-interval : (a ≤ b) → OpenInterval(a)(b)

data ClosedInterval (a : ℝ) (b : ℝ) : Stmt where
  closed-interval : (a ≤ b) → ClosedInterval(a)(b)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Properties on functions of ℝ

module Limit where
  postulate Limitₗ : (ℝ → ℝ) → ℝ → ℝ → Stmt
  -- Limitₗ = ∀{ε : ℝ₊} → ∃{ℝ₊}(δ ↦ ∀{x : ℝ} → )

module Continuity where
  postulate Continuous : (ℝ → ℝ) → Stmt

module Derivative where
  postulate Differentiable : (ℝ → ℝ) → Stmt

-- postulate Axiom1 : {x y : ℝ} → (x < y) → ¬ (y < x)
-- postulate Axiom2 : {x z : ℝ} → (x < z) → ∃(y ↦ (x < y) ∧ (y < z))
-- postulate Axiom4 : {x y z : ℝ} → ((x + y) + z) ≡ (x + (y + z))
-- postulate Axiom5 : {x y : ℝ} → ∃(z ↦ (x + z) ≡ y)
