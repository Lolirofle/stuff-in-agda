import Lvl

-- TODO: Just testing how it goes with creating an axiomatic system
module Geometry.Test3 (Point : Set(Lvl.𝟎)) where

open import Functional
open import Logic.Propositional{Lvl.𝟎}
open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
open import Relator.Equals{Lvl.𝟎}{Lvl.𝟎} renaming (_≡_ to _≡ₚ_ ; _≢_ to _≢ₚ_)
open import Sets.PredicateSet
open import Sets.PredicateSet.Proofs
open import Structure.Relator.Equivalence{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Relator.Ordering{Lvl.𝟎}{Lvl.𝟎}

-- A line of infinite length
record Line : Set(Lvl.𝟎) where
  constructor line
  field
    a : Point
    b : Point

  field
    different : (a ≢ₚ b)

-- A circle
record Circle : Set(Lvl.𝟎) where
  constructor circle
  field
    middle : Point
    outer : Point

record Theory : Set(Lvl.𝐒(Lvl.𝐒(Lvl.𝟎))) where
  -- Symbols
  field
    -- CirclesIntersectionPoint : Circle → Circle → Point → Set(Lvl.𝟎)
    _∈ᶜ_ : Point → Circle → Stmt
    _∈ˡ_ : Point → Line → Stmt

    -- circleIntersectionPoint : (a : Circle) → (b : Circle) → ⦃ _ : CircleIntersect a b ⦄ → Point

  CircleBoundary : Circle → Point → Stmt
  CircleBoundary c p = (p ∈ᶜ c) ∧ (∀{outer a : Point} → (a ∈ᶜ circle p outer) → ⊥)

  LineIntersection : Line → Line → Point → Stmt
  LineIntersection a b p = (p ∈ˡ a) ∧ (p ∈ˡ b)

  -- Axioms
  -- field
  --   circle-boundary-eq : ∀{a b} → ((_∈ᶜ a) ≡ (_∈ᶜ b)) ↔ (CircleBoundaryPoint a ≡ᵖ CircleBoundaryPoint b)
  --   circle-either : ∀{middle outer₁ outer₂} → ((_∈ᶜ circle middle outer₁) ⊆ (_∈ᶜ circle middle outer₂)) ∨ ((_∈ᶜ circle middle outer₂) ⊆ (_∈ᶜ circle middle outer₁))
    -- circleOuterIs Circle.outer

module Theorems ⦃ _ : Theory ⦄ where
  open Theory ⦃ ... ⦄

  -- perpendicularLine : CirclesIntersectionPoint

  -- middlepoint : Line → Point
  -- middlepoint(line(a)(b)) = 
