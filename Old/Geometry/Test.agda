import Lvl

-- TODO: Just testing how it goes with creating an axiomatic system
module Geometry.Test (Point : Set(Lvl.𝟎)) where

open import Functional
open import Logic.Propositional{Lvl.𝟎}
open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
open import Relator.Equals{Lvl.𝟎}{Lvl.𝟎}
-- open import Sets.Setoid.Uniqueness{Lvl.𝟎}{Lvl.𝟎}{Lvl.𝟎} hiding (Theorems)
open import Structure.Relator.Equivalence{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Relator.Ordering{Lvl.𝟎}{Lvl.𝟎}
-- open import Structure.Relator.Properties{Lvl.𝟎}{Lvl.𝟎} hiding (Theorems)

-- A line of infinite length
record Line : Set(Lvl.𝟎) where
  constructor line
  field
    a : Point
    b : Point

-- A line segment of finite length
record LineSegment : Set(Lvl.𝟎) where
  constructor lineSegment
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
    PointOnLineSegment : Point → LineSegment → Set(Lvl.𝟎) -- The point lies on the line segment
    PointOnCircle : Point → Circle → Set(Lvl.𝟎) -- The point lies on the circle
    _≾_ : LineSegment → LineSegment → Set(Lvl.𝟎) -- Comparison of line length

  _≿_ : LineSegment → LineSegment → Set(Lvl.𝟎) -- Comparison of line length
  _≿_ l₁ l₂ = l₂ ≾ l₁

  _≋_ : LineSegment → LineSegment → Set(Lvl.𝟎) -- Equality of line length
  _≋_ l₁ l₂ = (l₁ ≾ l₂) ∧ (l₁ ≿ l₂)

  -- Axioms
  field
    [≾]-weak-total-order : Weak.TotalOrder(_≾_)(_≋_) -- (_≾_) is a weak total order

    point-on-line-existence : ∀{l : Line} → ∃(p ↦ PointOnLine(p)(l)) -- There is a point on a line
    point1-on-line : ∀{l : Line} → PointOnLine(Line.a(l))(l)
    point2-on-line : ∀{l : Line} → PointOnLine(Line.b(l))(l)

    point-on-lineSegment-existence : ∀{l : LineSegment} → ∃(p ↦ PointOnLineSegment(p)(l)) -- There is a point on a line
    endpoint1-on-lineSegment : ∀{l : LineSegment} → PointOnLineSegment(Line.a(l))(l)
    endpoint2-on-lineSegment : ∀{l : LineSegment} → PointOnLineSegment(Line.b(l))(l)

    point-on-circle-existence : ∀{c : Circle} → ∃(p ↦ PointOnCircle(p)(c)) -- There is a point on a circle
    outer-on-circle : ∀{c : Circle} → PointOnCircle(Circle.outer(c))(c)
    single-point-circle : ∀{p : Point}{x : Point} → PointOnCircle(x) (circle(p)(p)) → (x ≡ p) -- There is only a simgle point on a circle of zero radius

    line-equality : ∀{l : Line}{a : Point}{b : Point} → PointOnLine(a)(l) → PointOnLine(b)(l) → (l ≡ line(a)(b)) -- A line is non-directional
    circle-equality : ∀{c : Circle}{o : Point} → PointOnCircle(o)(c) → (c ≡ circle(Circle.middle(c))(o))
    lineSegment-equality : ∀{a : Point}{b : Point} → (lineSegment(a)(b) ≡ lineSegment(b)(a)) -- A line segment is non-directional

    -- line-intersection : ∀{l₁ : Line}{l₂ : Line} → ∃!(p ↦ PointOnLine(p)(l₁) ∧ PointOnLine(p)(l₂))
    circle-intersection : ∀{a : Point}{b : Point} → ∃(i ↦ PointOnCircle(i)(circle(a)(b)) ∧ PointOnCircle(i)(circle(b)(a))) ∧ ∃(i ↦ PointOnCircle(i)(circle(a)(b)) ∧ PointOnCircle(i)(circle(b)(a)))

module Theorems ⦃ _ : Theory ⦄ where
  open Theory ⦃ ... ⦄

  -- middlepoint : Line → Point
  -- middlepoint(line(a)(b)) = 
