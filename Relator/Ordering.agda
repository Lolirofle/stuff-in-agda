open import Functional
import      Lang.Templates.Order as Template
open import Logic
open import Logic.Propositional
open import Type

module Relator.Ordering where

-- TODO: Maybe move everything here to Lang.Templates.Order

module From-[≤][<] {ℓ₁}{ℓ₂}{ℓ₃} {T : Type{ℓ₁}} (_≤_ : T → T → Stmt{ℓ₂}) (_<_ : T → T → Stmt{ℓ₃}) where
  open Template.From-[<] (_<_) public
  open Template.From-[≤] (_≤_) public

module From-[<][≡] {ℓ₁}{ℓ₂}{ℓ₃} {T : Type{ℓ₁}} (_<_ : T → T → Stmt{ℓ₂}) (_≡_ : T → T → Stmt{ℓ₃}) where
  _≤_ : T → T → Stmt
  x ≤ y = (x < y) ∨ (x ≡ y)

  open From-[≤][<] (_≤_)(_<_) public

module From-[≤][≢] {ℓ₁}{ℓ₂}{ℓ₃} {T : Type{ℓ₁}} (_≤_ : T → T → Stmt{ℓ₂}) (_≢_ : T → T → Stmt{ℓ₃}) where
  _<_ : T → T → Stmt
  x < y = (x ≤ y) ∧ (x ≢ y)

  open From-[≤][<] (_≤_)(_<_) public

module From-[≤] {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_≤_ : T → T → Stmt{ℓ₂}) where
  open Template.From-[≤] (_≤_) public

  _>_ : T → T → Stmt
  _>_ = _≰_
  open Template.From-[>] (_>_) public

module From-[<] {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_<_ : T → T → Stmt{ℓ₂}) where
  open Template.From-[<] (_<_) public

  _≥_ : T → T → Stmt
  _≥_ = _≮_
  open Template.From-[≥] (_≥_) public
