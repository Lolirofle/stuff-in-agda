module Relator.Names where

import      Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Numeral.Natural
open import Type

module _ {ℓ₁}{ℓ₂}{ℓ₃}{ℓ₄} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} where
  ConversePattern : (T₁ → T₂ → Stmt{ℓ₃}) → (T₂ → T₁ → Stmt{ℓ₄}) → Stmt
  ConversePattern (_▫₁_) (_▫₂_) = (∀{x : T₁}{y : T₂} → (x ▫₁ y) → (y ▫₂ x))

module _ {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  Symmetry : Stmt
  Symmetry = ConversePattern (_▫_) (_▫_)

  Asymmetry : Stmt
  Asymmetry = ConversePattern (_▫_) (x ↦ y ↦ ¬(x ▫ y))

  Reflexivity : Stmt
  Reflexivity = ∀{x : T} → (x ▫ x)

  Transitivity : Stmt
  Transitivity = ∀{x y z : T} → (x ▫ y) → (y ▫ z) → (x ▫ z)

  Irreflexivity : Stmt
  Irreflexivity = ∀{x : T} → ¬(x ▫ x)

  ConverseTotal : Stmt
  ConverseTotal = ∀{x y : T} → (x ▫ y) ∨ (y ▫ x)

  ConverseDichotomy : Stmt
  ConverseDichotomy = {x y : T} → (x ▫ y) ⊕ (y ▫ x)

module _ {ℓ₁}{ℓ₂}{ℓ₃} {T : Type{ℓ₁}} (_▫₁_ : T → T → Stmt{ℓ₂}) (_▫₂_ : T → T → Stmt{ℓ₃}) where
  Antisymmetry : Stmt
  Antisymmetry = ∀{a b : T} → (a ▫₁ b) → (b ▫₁ a) → (a ▫₂ b)

-- Trichotomy : {T : Type} → (T → T → Stmt) → Stmt
-- Trichotomy {T} (_▫₁_) (_▫₂_) = {x y : T} → (x ▫₁ y) ⊕ (y ▫₁ x) ⊕ (x ▫₂ y) -- TODO: Not correct. Should only be one of them
