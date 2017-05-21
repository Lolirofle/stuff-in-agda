module Numeral.Real where

import Level as Lvl
open import Data
open import Functional
open import Logic.Propositional{Lvl.𝟎}
open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
open import Numeral.Integer hiding (𝟎 ; −_ ; abs)
open import Numeral.Natural
open import Structure.Operator.Field{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Operator.Group{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Operator.Properties{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Relator.Ordering{Lvl.𝟎}{Lvl.𝟎}

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
open [ℝ]-conversion ⦃ ... ⦄ public

instance postulate [ℕ]-to-[ℝ] : [ℝ]-conversion(ℕ)
instance postulate [ℤ]-to-[ℝ] : [ℝ]-conversion(ℤ)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Elements]

postulate e : ℝ
postulate π : ℝ
postulate 𝑖 : ℝ -- TODO: Let's pretend because I am lazy

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Operators]

infixl 1000 _+_ _−_
infixl 1001 _⋅_ _/_
infixl 1002 _^_ _√_
postulate _+_ : ℝ → ℝ → ℝ
postulate _−_ : ℝ → ℝ → ℝ
postulate _⋅_ : ℝ → ℝ → ℝ
postulate _/_ : ℝ → ℝ → ℝ -- TODO: Some of these are either partial functions or have a smaller domain
postulate _^_ : ℝ → ℝ → ℝ
postulate log : ℝ → ℝ → ℝ
postulate _√_ : ℝ → ℝ → ℝ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Functions]

abs : ℝ → ℝ
abs(x) = #(2) √ (x ^ #(2))

postulate sin : ℝ → ℝ
postulate cos : ℝ → ℝ

tan : ℝ → ℝ
tan(x) = sin(x) / cos(x)

postulate asin : ℝ → ℝ
postulate acos : ℝ → ℝ
postulate atan : ℝ → ℝ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Relations]

-- infixr 100 _≡_ _≢_ _<_ _>_ _≤_ _≥_ _<_<_

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

-- In an open interval
_<_<_ : ℝ → ℝ → ℝ → Stmt
x < y < z = (x < y) ∧ (y < z)

-- In an closed interval
_≤_≤_ : ℝ → ℝ → ℝ → Stmt
x ≤ y ≤ z = (x ≤ y) ∧ (y ≤ z)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Properties of operations in ℝ]

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
-- [Properties of relations in ℝ]

instance
  postulate [ℝ][≤][≡]-totalWeakPartialOrder : TotalWeakPartialOrder {ℝ} (_≤_)(_≡_)

instance
  postulate [ℝ][<]-strictPartialOrder       : StrictPartialOrder {ℝ} (_<_)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Properties of functions in ℝ]

instance postulate abs-positive : ∀{x} → (abs(x) ≥ #(0))
instance postulate cos-periodicity : ∀{v}{n : ℕ} → (cos(v) ≡ cos(v + #(2) ⋅ π ⋅ #(n)))
instance postulate sin-periodicity : ∀{v}{n : ℕ} → (sin(v) ≡ sin(v + #(2) ⋅ π ⋅ #(n)))
instance postulate cos-even : ∀{v} → (cos(v) ≡ cos(#(0) − v))
instance postulate sin-odd  : ∀{v} → (sin(v) ≡ #(0) − sin(#(0) − v))
instance postulate circle : ∀{v} → (cos(v) ^ #(2) + sin(v) ^ #(2) ≡ #(1))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Data structures]

data ℝ-subset (P : ℝ → Stmt) : Set where
  subelem : ∀(x : ℝ) → ⦃ _ : P(x) ⦄ → ℝ-subset(P)

-- Positive real numbers
ℝ₊ = ℝ-subset(x ↦ (x > #(0)))

instance
  subset-to-[ℝ] : ∀{P} → [ℝ]-conversion(ℝ-subset(P))
  subset-to-[ℝ] {P} = record{#_ = f} where
    f : ℝ-subset(P) → ℝ
    f(subelem x) = x

data OpenInterval (a : ℝ) (b : ℝ) : Set where
  open-interval : (a ≤ b) → OpenInterval(a)(b)

data ClosedInterval (a : ℝ) (b : ℝ) : Set where
  closed-interval : (a ≤ b) → ClosedInterval(a)(b)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- [Properties on functions of ℝ]

module Limit where
  -- Statement that the limit of the function f at point l exists (and its value is L)
  data Limit (f : ℝ → ℝ) (p : ℝ) : Stmt where
    limit : (L : ℝ) → (∀{ε : ℝ₊} → ∃{ℝ₊}(δ ↦ ∀{x : ℝ} → (#(0) < abs(x − p) < #(δ)) → (abs(f(x) − L) < #(ε)))) → Limit f(p)

  -- Limit value functio§n f (if the limit exists)
  lim : (f : ℝ → ℝ) → (x : ℝ) → ⦃ _ : Limit f(x) ⦄ → ℝ
  lim _ _ ⦃ limit L _ ⦄ = L

module Continuity where
  open Limit

  -- Statement that the point x of function f is a continous point
  ContinuousPoint : (ℝ → ℝ) → ℝ → Stmt
  ContinuousPoint f(x) = (⦃ limit : Limit f(x) ⦄ → (lim f(x)⦃ limit ⦄ ≡ f(x)))

  -- Statement that the function f is continous
  Continuous : (ℝ → ℝ) → Stmt
  Continuous f = ∀{x} → ContinuousPoint f(x)

module Derivative where
  open Limit using (Limit ; limit ; lim)

  -- Statement that the point x of function f is a differentiable point
  DifferentiablePoint : (ℝ → ℝ) → ℝ → Stmt
  DifferentiablePoint f(p) = Limit(x ↦ ((f(x) − f(p))/(x − p)))(p)

  -- Statement that function f is differentiable
  Differentiable : (ℝ → ℝ) → Stmt
  Differentiable f = ∀{x} → DifferentiablePoint f(x)

  -- Derivative value of function f at point x (if the point is differentiable)
  𝐷 : (f : ℝ → ℝ) → (x : ℝ) → ⦃ _ : DifferentiablePoint f(x) ⦄ → ℝ
  𝐷 _ _ ⦃ limit D _ ⦄ = D

-- postulate Axiom1 : {x y : ℝ} → (x < y) → ¬ (y < x)
-- postulate Axiom2 : {x z : ℝ} → (x < z) → ∃(y ↦ (x < y) ∧ (y < z))
-- postulate Axiom4 : {x y z : ℝ} → ((x + y) + z) ≡ (x + (y + z))
-- postulate Axiom5 : {x y : ℝ} → ∃(z ↦ (x + z) ≡ y)
