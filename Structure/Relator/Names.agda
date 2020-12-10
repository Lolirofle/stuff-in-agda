module Structure.Relator.Names where

import      Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Xor
open import Numeral.Natural
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Lvl.Level
private variable T A B C D E : Type{ℓ}

ConversePattern : (A → B → Stmt{ℓ₁}) → (B → A → Stmt{ℓ₂}) → Stmt
ConversePattern(_▫₁_)(_▫₂_) = ∀{x}{y} → (x ▫₁ y) → (y ▫₂ x)

Subrelation : (A → B → Stmt{ℓ₁}) → (A → B → Stmt{ℓ₂}) → Stmt
Subrelation(_▫₁_)(_▫₂_) = ∀{x}{y} → (x ▫₁ y) → (x ▫₂ y)

TransitivityPattern : (A → B → Stmt{ℓ₁}) → (B → C → Stmt{ℓ₂}) → (A → C → Stmt{ℓ₃}) → Stmt
TransitivityPattern(_▫₁_)(_▫₂_)(_▫₃_) = ∀{x}{y}{z} → (x ▫₁ y) → (y ▫₂ z) → (x ▫₃ z)

FlippedTransitivityₗPattern : (A → C → Stmt{ℓ₁}) → (B → C → Stmt{ℓ₂}) → (A → B → Stmt{ℓ₃}) → Stmt
FlippedTransitivityₗPattern(_▫₁_)(_▫₂_)(_▫₃_) = ∀{x}{y}{z} → (x ▫₁ z) → (y ▫₂ z) → (x ▫₃ y)

FlippedTransitivityᵣPattern : (A → B → Stmt{ℓ₁}) → (A → C → Stmt{ℓ₂}) → (B → C → Stmt{ℓ₃}) → Stmt
FlippedTransitivityᵣPattern(_▫₁_)(_▫₂_)(_▫₃_) = ∀{x}{y}{z} → (x ▫₁ y) → (x ▫₂ z) → (y ▫₃ z)

module _ (_▫_ : T → T → Stmt{ℓ}) where
  Symmetry : Stmt
  Symmetry = ConversePattern(_▫_)(_▫_)

  Asymmetry : Stmt
  Asymmetry = ConversePattern(_▫_)((¬_) ∘₂ (_▫_))

  Reflexivity : Stmt
  Reflexivity = ∀{x : T} → (x ▫ x)

  Transitivity : Stmt
  Transitivity = TransitivityPattern(_▫_)(_▫_)(_▫_)

  SwappedTransitivity : Stmt
  SwappedTransitivity = ∀{x y z : T} → (y ▫ z) → (x ▫ y) → (x ▫ z)

  -- Also called: Left Euclidean
  FlippedTransitivityₗ : Stmt
  FlippedTransitivityₗ = FlippedTransitivityₗPattern(_▫_)(_▫_)(_▫_)

  -- Also called: Right Euclidean
  FlippedTransitivityᵣ : Stmt
  FlippedTransitivityᵣ = FlippedTransitivityᵣPattern(_▫_)(_▫_)(_▫_)

  Irreflexivity : Stmt
  Irreflexivity = ∀{x : T} → ¬(x ▫ x)

  ConverseTotal : Stmt
  ConverseTotal = ∀{x y : T} → (x ▫ y) ∨ (y ▫ x)

  ConverseDichotomy : Stmt
  ConverseDichotomy = {x y : T} → (x ▫ y) ⊕ (y ▫ x)

module _ (_▫₁_ : T → T → Stmt{ℓ₁}) (_▫₂_ : T → T → Stmt{ℓ₂}) where
  Antisymmetry : Stmt
  Antisymmetry = ∀{a b} → (a ▫₁ b) → (b ▫₁ a) → (a ▫₂ b)

  Trichotomy : Stmt
  Trichotomy = ∀{x y} → (x ▫₁ y) ⊕₃ (y ▫₁ x) ⊕₃ (x ▫₂ y)

module _ (_▫₁_ : A → B → Stmt{ℓ₁}) (_▫₂_ : A → A → Stmt{ℓ₂}) where
  Subtransitivityₗ : Stmt
  Subtransitivityₗ = TransitivityPattern(_▫₂_)(_▫₁_)(_▫₁_)

module _ (_▫₁_ : A → B → Stmt{ℓ₁}) (_▫₂_ : B → B → Stmt{ℓ₂}) where
  Subtransitivityᵣ : Stmt
  Subtransitivityᵣ = TransitivityPattern(_▫₁_)(_▫₂_)(_▫₁_)
