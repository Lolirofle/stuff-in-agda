module Structure.Relator.Names where

import      Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Function
open import Functional
open import Functional.Instance
open import Logic
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Xor
open import Numeral.Natural
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Lvl.Level
private variable T A B C D E : Type{ℓ}

SubPattern₁ : (B → C → Type{ℓ}) → (A → B) → (A → C) → Type
SubPattern₁(_▫_) = ∀ₗ ∘₂ pointwise₂,₁(_▫_)

-- Expanded definition: ∀{x}{y} → ((x ▫₁ y) ▫ (x ▫₂ y))
SubPattern₂ : (C → D → Stmt{ℓ}) → (A → B → C) → (A → B → D) → Stmt
SubPattern₂(_▫_) = ∀ₗ ∘₂ (∀ₗ ∘₃ pointwise₂,₂(_▫_))

SubPattern₃ : (D → E → Stmt{ℓ}) → (A → B → C → D) → (A → B → C → E) → Stmt
SubPattern₃(_▫_) = ∀ₗ ∘₂ (∀ₗ ∘₃ (∀ₗ ∘₄ pointwise₂,₃(_▫_)))

TransitivityPattern : (A → B → Stmt{ℓ₁}) → (B → C → Stmt{ℓ₂}) → (A → C → Stmt{ℓ₃}) → Stmt
TransitivityPattern(_▫₁_)(_▫₂_)(_▫₃_) = ∀{x}{y}{z} → (x ▫₁ y) → (y ▫₂ z) → (x ▫₃ z) -- TODO: If written (∀{x}{y}{z} → ((x ▫₁ y) ▫₄ (y ▫₂ z)) ▫₅ (x ▫₃ z)) (similar to how SubPattern₂ is generalized from Sub₂), then triangle inquality is also a special case. But that is a special case from (∀{x}{y}{z} → ((▫₁ x y z) ▫₄ (▫₂ x y z)) ▫₅ (▫₃ x y z)) (generalizing flipped transitivity), which is a special case from (∀{x}{y}{z} → (▫₁ x y z) ▫₅ (▫₂ x y z)) (generalizing cotransitivity and everything using three variables).

FlippedTransitivityₗPattern : (A → C → Stmt{ℓ₁}) → (B → C → Stmt{ℓ₂}) → (A → B → Stmt{ℓ₃}) → Stmt
FlippedTransitivityₗPattern(_▫₁_)(_▫₂_)(_▫₃_) = ∀{x}{y}{z} → (x ▫₁ z) → (y ▫₂ z) → (x ▫₃ y)

FlippedTransitivityᵣPattern : (A → B → Stmt{ℓ₁}) → (A → C → Stmt{ℓ₂}) → (B → C → Stmt{ℓ₃}) → Stmt
FlippedTransitivityᵣPattern(_▫₁_)(_▫₂_)(_▫₃_) = ∀{x}{y}{z} → (x ▫₁ y) → (x ▫₂ z) → (y ▫₃ z)

Sub₁ : (A → Stmt{ℓ₁}) → (A → Stmt{ℓ₂}) → Stmt
Sub₁ = SubPattern₁(_→ᶠ_)

Sub₂ : (A → B → Stmt{ℓ₁}) → (A → B → Stmt{ℓ₂}) → Stmt
Sub₂ = SubPattern₂(_→ᶠ_)

Sub₃ : (A → B → C → Stmt{ℓ₁}) → (A → B → C → Stmt{ℓ₂}) → Stmt
Sub₃ = SubPattern₃(_→ᶠ_)

module _ (_▫_ : T → T → Stmt{ℓ}) where
  -- Expanded definition: ∀{x y} → (x ▫ y) → (y ▫ x)
  Symmetry : Stmt
  Symmetry = Sub₂(_▫_)(swap(_▫_))

  -- Expanded definition: ∀{x y} → (x ▫ y) → ¬(y ▫ x)
  Asymmetry : Stmt
  Asymmetry = Sub₂(_▫_)(swap((¬_) ∘₂ (_▫_)))

  -- Expanded definition: ∀{x : T} → (x ▫ x)
  Reflexivity : Stmt
  Reflexivity = ∀{x} → ((_▫_) $₂ x)

  -- Expanded definition: ∀{x : T} → ¬(x ▫ x)
  Irreflexivity : Stmt
  Irreflexivity = ∀{x} → (((¬_) ∘₂ (_▫_)) $₂ x)

  -- Expanded definition: ∀{x y} → (x ▫ y) → (y ▫ z) → (x ▫ z)
  Transitivity : Stmt
  Transitivity = TransitivityPattern(_▫_)(_▫_)(_▫_)

  SwappedTransitivity : Stmt
  SwappedTransitivity = ∀{x y z : T} → (y ▫ z) → (x ▫ y) → (x ▫ z)

  -- Also called: Left Euclidean.
  FlippedTransitivityₗ : Stmt
  FlippedTransitivityₗ = FlippedTransitivityₗPattern(_▫_)(_▫_)(_▫_)

  -- Also called: Right Euclidean.
  FlippedTransitivityᵣ : Stmt
  FlippedTransitivityᵣ = FlippedTransitivityᵣPattern(_▫_)(_▫_)(_▫_)

  -- Also called: Total, complete, connex.
  ConverseTotal : Stmt
  ConverseTotal = SubPattern₂(_∨_)(_▫_)(swap(_▫_))

  ConverseDichotomy : Stmt
  ConverseDichotomy = SubPattern₂(_⊕_)(_▫_)(swap(_▫_))

  -- Also called: Comparison.
  CoTransitivity : Stmt
  CoTransitivity = ∀{x y z : T} → (x ▫ z) → ((x ▫ y) ∨ (y ▫ z))

module _ (_▫₁_ : T → T → Stmt{ℓ₁}) (_▫₂_ : T → T → Stmt{ℓ₂}) where
  Antisymmetry : Stmt
  Antisymmetry = ∀{a b} → (a ▫₁ b) → (b ▫₁ a) → (a ▫₂ b)

  ConverseTrichotomy : Stmt
  ConverseTrichotomy = ∀{x y} → (x ▫₁ y) ∨ (x ▫₂ y) ∨ (y ▫₁ x)

module _ (_▫₁_ : A → B → Stmt{ℓ₁}) (_▫₂_ : A → A → Stmt{ℓ₂}) where
  Subtransitivityₗ : Stmt
  Subtransitivityₗ = TransitivityPattern(_▫₂_)(_▫₁_)(_▫₁_)

module _ (_▫₁_ : A → B → Stmt{ℓ₁}) (_▫₂_ : B → B → Stmt{ℓ₂}) where
  Subtransitivityᵣ : Stmt
  Subtransitivityᵣ = TransitivityPattern(_▫₁_)(_▫₂_)(_▫₁_)
