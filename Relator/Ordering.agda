open import Functional
open import Logic
open import Logic.Propositional
open import Type

module Relator.Ordering where

module From-[<][≡] {ℓ₁}{ℓ₂}{ℓ₃} {T : Type{ℓ₁}} (_<_ : T → T → Stmt{ℓ₂}) (_≡_ : T → T → Stmt{ℓ₃}) where
  -- Greater than
  _>_ : T → T → Stmt
  _>_ = swap(_<_)

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
  _≮_ = (¬_) ∘₂ (_<_)

  _≯_ : T → T → Stmt
  _≯_ = (¬_) ∘₂ (_>_)

  _≰_ : T → T → Stmt
  _≰_ = (¬_) ∘₂ (_≤_)

  _≱_ : T → T → Stmt
  _≱_ = (¬_) ∘₂ (_≥_)

module From-[≤] {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_≤_ : T → T → Stmt{ℓ₂}) where
  -- Greater than or equals
  _≥_ : T → T → Stmt
  _≥_ = swap(_≤_)

  _≰_ : T → T → Stmt
  _≰_ = (¬_) ∘₂ (_≤_)

  _≱_ : T → T → Stmt
  _≱_ = swap(_≰_)

  -- Greater than
  _>_ : T → T → Stmt
  _>_ = _≰_

  -- Lesser than or equals
  _<_ : T → T → Stmt
  _<_ = swap(_>_)

  -- In an open interval
  _<_<_ : T → T → T → Stmt
  x < y < z = (x < y) ∧ (y < z)

  -- In an closed interval
  _≤_≤_ : T → T → T → Stmt
  x ≤ y ≤ z = (x ≤ y) ∧ (y ≤ z)

  _≮_ : T → T → Stmt
  _≮_ = (¬_) ∘₂ (_<_)

  _≯_ : T → T → Stmt
  _≯_ = (¬_) ∘₂ (_>_)

module From-[≤][<] {ℓ₁}{ℓ₂}{ℓ₃} {T : Type{ℓ₁}} (_≤_ : T → T → Stmt{ℓ₂}) (_<_ : T → T → Stmt{ℓ₃}) where
  -- Greater than
  _>_ : T → T → Stmt
  _>_ = swap(_<_)

  -- Greater than or equals
  _≥_ : T → T → Stmt
  _≥_ = swap(_≤_)

  -- In an open interval
  _<_<_ : T → T → T → Stmt
  x < y < z = (x < y) ∧ (y < z)

  -- In an closed interval
  _≤_≤_ : T → T → T → Stmt
  x ≤ y ≤ z = (x ≤ y) ∧ (y ≤ z)

  _≮_ : T → T → Stmt
  _≮_ = (¬_) ∘₂ (_<_)

  _≯_ : T → T → Stmt
  _≯_ = (¬_) ∘₂ (_>_)

  _≰_ : T → T → Stmt
  _≰_ = (¬_) ∘₂ (_≤_)

  _≱_ : T → T → Stmt
  _≱_ = (¬_) ∘₂ (_≥_)

module From-[≤][≢] {ℓ₁}{ℓ₂}{ℓ₃} {T : Type{ℓ₁}} (_≤_ : T → T → Stmt{ℓ₂}) (_≢_ : T → T → Stmt{ℓ₃}) where
  -- Lesser than or equals
  _<_ : T → T → Stmt
  x < y = (x ≤ y) ∧ (x ≢ y)

  -- Greater than
  _>_ : T → T → Stmt
  _>_ = swap(_<_)

  -- Greater than or equals
  _≥_ : T → T → Stmt
  _≥_ = swap(_≤_)

  -- In an open interval
  _<_<_ : T → T → T → Stmt
  x < y < z = (x < y) ∧ (y < z)

  -- In an closed interval
  _≤_≤_ : T → T → T → Stmt
  x ≤ y ≤ z = (x ≤ y) ∧ (y ≤ z)

  _≮_ : T → T → Stmt
  _≮_ = (¬_) ∘₂ (_<_)

  _≯_ : T → T → Stmt
  _≯_ = (¬_) ∘₂ (_>_)

  _≰_ : T → T → Stmt
  _≰_ = (¬_) ∘₂ (_≤_)

  _≱_ : T → T → Stmt
  _≱_ = (¬_) ∘₂ (_≥_)
