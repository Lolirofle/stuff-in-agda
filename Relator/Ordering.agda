open import Logic
open import Logic.Propositional
open import Type

module Relator.Ordering where

module From-[<][≡] {ℓ₁}{ℓ₂}{ℓ₃} {T : Type{ℓ₁}} (_<_ : T → T → Stmt{ℓ₂}) (_≡_ : T → T → Stmt{ℓ₃}) where
  -- Greater than
  _>_ : T → T → Stmt
  x > y = y < x

  -- Lesser than or equals
  _≤_ : T → T → Stmt
  x ≤ y = (x < y) ∨ (x ≡ y)

  -- Greater than or equals
  _≥_ : T → T → Stmt
  x ≥ y = (x > y) ∨ (x ≡ y)

  -- In an open interval
  _<_<_ : T → T → T → Stmt
  x < y < z = (x < y) ∧ (y < z)

  -- In an closed interval
  _≤_≤_ : T → T → T → Stmt
  x ≤ y ≤ z = (x ≤ y) ∧ (y ≤ z)

  _≮_ : T → T → Stmt
  x ≮ y = ¬(x < y)

  _≯_ : T → T → Stmt
  x ≯ y = ¬(x > y)

  _≰_ : T → T → Stmt
  x ≰ y = ¬(x ≤ y)

  _≱_ : T → T → Stmt
  x ≱ y = ¬(x ≥ y)

module From-[≤] {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_≤_ : T → T → Stmt{ℓ₂}) where
  -- Greater than
  _>_ : T → T → Stmt
  x > y = ¬(x ≤ y)

  -- Lesser than or equals
  _<_ : T → T → Stmt
  x < y = (y > x)

  -- Greater than or equals
  _≥_ : T → T → Stmt
  x ≥ y = (y ≤ x)

  -- In an open interval
  _<_<_ : T → T → T → Stmt
  x < y < z = (x < y) ∧ (y < z)

  -- In an closed interval
  _≤_≤_ : T → T → T → Stmt
  x ≤ y ≤ z = (x ≤ y) ∧ (y ≤ z)

  _≮_ : T → T → Stmt
  x ≮ y = ¬(x < y)

  _≯_ : T → T → Stmt
  x ≯ y = (x ≤ y)

  _≰_ : T → T → Stmt
  x ≰ y = ¬(x ≤ y)

  _≱_ : T → T → Stmt
  x ≱ y = ¬(x ≥ y)

module From-[≤][<] {ℓ₁}{ℓ₂}{ℓ₃} {T : Type{ℓ₁}} (_≤_ : T → T → Stmt{ℓ₂}) (_<_ : T → T → Stmt{ℓ₃}) where
  -- Greater than
  _>_ : T → T → Stmt
  x > y = (y < x)

  -- Greater than or equals
  _≥_ : T → T → Stmt
  x ≥ y = (y ≤ x)

  -- In an open interval
  _<_<_ : T → T → T → Stmt
  x < y < z = (x < y) ∧ (y < z)

  -- In an closed interval
  _≤_≤_ : T → T → T → Stmt
  x ≤ y ≤ z = (x ≤ y) ∧ (y ≤ z)

  _≮_ : T → T → Stmt
  x ≮ y = ¬(x < y)

  _≯_ : T → T → Stmt
  x ≯ y = ¬(x > y)

  _≰_ : T → T → Stmt
  x ≰ y = ¬(x ≤ y)

  _≱_ : T → T → Stmt
  x ≱ y = ¬(x ≥ y)

module From-[≤][≡] {ℓ₁}{ℓ₂}{ℓ₃} {T : Type{ℓ₁}} (_≤_ : T → T → Stmt{ℓ₂}) (_≡_ : T → T → Stmt{ℓ₃}) where
  -- Lesser than or equals
  _<_ : T → T → Stmt
  x < y = (x ≤ y) ∧ ¬(x ≡ y)

  -- Greater than
  _>_ : T → T → Stmt
  x > y = (y < x)

  -- Greater than or equals
  _≥_ : T → T → Stmt
  x ≥ y = (y ≤ x)

  -- In an open interval
  _<_<_ : T → T → T → Stmt
  x < y < z = (x < y) ∧ (y < z)

  -- In an closed interval
  _≤_≤_ : T → T → T → Stmt
  x ≤ y ≤ z = (x ≤ y) ∧ (y ≤ z)

  _≮_ : T → T → Stmt
  x ≮ y = ¬(x < y)

  _≯_ : T → T → Stmt
  x ≯ y = ¬(x > y)

  _≰_ : T → T → Stmt
  x ≰ y = ¬(x ≤ y)

  _≱_ : T → T → Stmt
  x ≱ y = ¬(x ≥ y)
