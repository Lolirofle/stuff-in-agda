import Lvl

-- TODO: Just testing how it goes with creating an axiomatic system
module Geometry.Test2 (Point : Set(Lvl.𝟎)) where

open import Functional
open import Logic.Propositional{Lvl.𝟎}
open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
open import Relator.Equals{Lvl.𝟎}{Lvl.𝟎}
-- open import Structure.Setoid.Uniqueness{Lvl.𝟎}{Lvl.𝟎}{Lvl.𝟎} hiding (Theorems)
open import Structure.Relator.Equivalence{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Relator.Ordering{Lvl.𝟎}{Lvl.𝟎}
-- open import Structure.Relator.Properties{Lvl.𝟎}{Lvl.𝟎} hiding (Theorems)

-- A line of finite length
record Line : Set(Lvl.𝟎) where
  constructor line
  field
    a : Point
    b : Point

-- A circle
record Circle : Set(Lvl.𝟎) where
  constructor circle
  field
    middle : Point
    outer : Point

record Theory : Set(Lvl.𝐒(Lvl.𝟎)) where
  -- Symbols
  field
    PointOnLine : Point → Line → Set(Lvl.𝟎) -- The point lies on the line
    PointOnCircle : Point → Circle → Set(Lvl.𝟎) -- The point lies on the circle
    _≾_ : Line → Line → Set(Lvl.𝟎) -- Comparison of line length

  _≿_ : Line → Line → Set(Lvl.𝟎) -- Comparison of line length
  _≿_ l₁ l₂ = l₂ ≾ l₁

  _≋_ : Line → Line → Set(Lvl.𝟎) -- Equality of line length
  _≋_ l₁ l₂ = (l₁ ≾ l₂) ∧ (l₁ ≿ l₂)

  -- Axioms
  field
    [≾]-weak-total-order : Weak.TotalOrder(_≾_)(_≋_) -- (_≾_) is a weak total order

    point-on-line-existence : ∀{l : Line} → ∃(p ↦ PointOnLine(p)(l)) -- There is a point on a line
    endpoint1-on-line : ∀{l : Line} → PointOnLine(Line.a(l))(l)
    endpoint2-on-line : ∀{l : Line} → PointOnLine(Line.b(l))(l)
    single-point-line : ∀{p : Point}{x : Point} → PointOnLine(x) (line(p)(p)) → (x ≡ p) -- There is only a simgle point on a line of zero length

    point-on-circle-existence : ∀{c : Circle} → ∃(p ↦ PointOnCircle(p)(c)) -- There is a point on a circle
    outer-on-circle : ∀{c : Circle} → PointOnCircle(Circle.outer(c))(c)
    single-point-circle : ∀{p : Point}{x : Point} → PointOnCircle(x) (circle(p)(p)) → (x ≡ p) -- There is only a simgle point on a circle of zero radius

    line-symmetry : ∀{a : Point}{b : Point} → (line(a)(b) ≡ line(b)(a)) -- A line is non-directional

    circle-intersection : ∀{a : Point}{b : Point} → ∃(i ↦ PointOnCircle(i)(circle(a)(b)) ∧ PointOnCircle(i)(circle(b)(a))) ∧ ∃(i ↦ PointOnCircle(i)(circle(a)(b)) ∧ PointOnCircle(i)(circle(b)(a)))

module Theorems ⦃ _ : Theory ⦄ where
  open Theory ⦃ ... ⦄

  -- middlepoint : Line → Point
  -- middlepoint(line(a)(b)) = 
