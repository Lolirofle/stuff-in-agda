open import Functional
open import Logic
open import Logic.Propositional
open import Type

module Lang.Templates.Order {ℓ} {T : Type{ℓ}} where

import Lvl

private variable ℓₗ : Lvl.Level

-------------------------------------------------------------------------------
-- ≤

module Multi-from-[≤] (_≤_ : T → T → Stmt{ℓₗ}) where
  _≤_≤_ : T → T → T → Stmt
  x ≤ y ≤ z = (x ≤ y) ∧ (y ≤ z)

  _≤_≤_≤_ : T → T → T → T → Stmt
  x ≤ y ≤ z ≤ w = (x ≤ y) ∧ (y ≤ z) ∧ (z ≤ w)

module [¬]-from-[≤] (_≤_ : T → T → Stmt{ℓₗ}) where
  _≰_ : T → T → Stmt
  _≰_ = (¬_) ∘₂ (_≤_)

-------------------------------------------------------------------------------
-- ≥

module Multi-from-[≥] {ℓₗ} (_≥_ : T → T → Stmt{ℓₗ}) = Multi-from-[≤] (_≥_)
  renaming(
    _≤_≤_ to _≥_≥_ ;
    _≤_≤_≤_ to _≥_≥_≥_
  )

module [¬]-from-[≥] {ℓₗ} (_≥_ : T → T → Stmt{ℓₗ}) = [¬]-from-[≤] (_≥_)
  renaming(
    _≰_ to _≱_
  )

-------------------------------------------------------------------------------
-- <

module Multi-from-[<] {ℓₗ} (_<_ : T → T → Stmt{ℓₗ}) = Multi-from-[≤] (_<_)
  renaming(
    _≤_≤_ to _<_<_ ;
    _≤_≤_≤_ to _<_<_<_
  )

module [¬]-from-[<] {ℓₗ} (_<_ : T → T → Stmt{ℓₗ}) = [¬]-from-[≤] (_<_)
  renaming(
    _≰_ to _≮_
  )

-------------------------------------------------------------------------------
-- >

module Multi-from-[>] {ℓₗ} (_>_ : T → T → Stmt{ℓₗ}) = Multi-from-[≤] (_>_)
  renaming(
    _≤_≤_ to _>_>_ ;
    _≤_≤_≤_ to _>_>_>_
  )

module [¬]-from-[>] {ℓₗ} (_>_ : T → T → Stmt{ℓₗ}) = [¬]-from-[≤] (_>_)
  renaming(
    _≰_ to _≯_
  )

-------------------------------------------------------------------------------
-- Combinations

module From-[<] (_<_ : T → T → Stmt{ℓₗ}) where
  open Multi-from-[<] (_<_) public
  open [¬]-from-[<]   (_<_) public

  _>_ : T → T → Stmt
  _>_ = swap(_<_)
  open Multi-from-[>] (_>_) public
  open [¬]-from-[>]   (_>_) public

module From-[>] (_>_ : T → T → Stmt{ℓₗ}) where
  open Multi-from-[>] (_>_) public
  open [¬]-from-[>]   (_>_) public

  _<_ : T → T → Stmt
  _<_ = swap(_>_)
  open Multi-from-[<] (_<_) public
  open [¬]-from-[<]   (_<_) public

module From-[≤] (_≤_ : T → T → Stmt{ℓₗ}) where
  open Multi-from-[≤] (_≤_) public
  open [¬]-from-[≤]   (_≤_) public

  _≥_ : T → T → Stmt
  _≥_ = swap(_≤_)
  open Multi-from-[≥] (_≥_) public
  open [¬]-from-[≥]   (_≥_) public

module From-[≥] (_≥_ : T → T → Stmt{ℓₗ}) where
  open Multi-from-[≥] (_≥_) public
  open [¬]-from-[≥]   (_≥_) public

  _≤_ : T → T → Stmt
  _≤_ = swap(_≥_)
  open Multi-from-[≤] (_≤_) public
  open [¬]-from-[≤]   (_≤_) public
