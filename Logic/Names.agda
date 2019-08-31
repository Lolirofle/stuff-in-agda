module Logic.Names where

open import Logic
open import Logic.Predicate
open import Logic.Propositional

module _ {ℓ} where
  ExcludedMiddleOn : Stmt{ℓ} → Stmt
  ExcludedMiddleOn(X) = (X ∨ (¬ X))
  ExcludedMiddle = ∀ᶠ(ExcludedMiddleOn)

  NonContradictionOn : Stmt{ℓ} → Stmt
  NonContradictionOn(X) = ¬(X ∧ (¬ X))
  NonContradiction = ∀ᶠ(NonContradictionOn)

  DoubleNegationOn : Stmt{ℓ} → Stmt
  DoubleNegationOn(X) = (¬(¬ X)) → X
  DoubleNegation = ∀ᶠ(DoubleNegationOn)

module _ {ℓ₁ ℓ₂} where
  CallCCOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  CallCCOn(X)(Y) = (((X → Y) → X) → X)
  CallCC = ∀²ᶠ(CallCCOn)

  ContrapositiveOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  ContrapositiveOn(X)(Y) = (X → Y) → ((¬ Y) → (¬ X))
  Contrapositive = ∀²ᶠ(ContrapositiveOn)

  DisjunctiveSyllogismₗOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  DisjunctiveSyllogismₗOn(X)(Y) = ((X ∨ Y) ∧ (¬ Y)) → X
  DisjunctiveSyllogismₗ = ∀²ᶠ(DisjunctiveSyllogismₗOn)

  DisjunctiveSyllogismᵣOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  DisjunctiveSyllogismᵣOn(X)(Y) = ((X ∨ Y) ∧ (¬ X)) → Y
  DisjunctiveSyllogismᵣ = ∀²ᶠ(DisjunctiveSyllogismᵣOn)

  MaterialImplicationOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  MaterialImplicationOn(X)(Y) = (X → Y) ↔ ((¬ X) ∨ Y)
  MaterialImplication = ∀²ᶠ(MaterialImplicationOn)

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} where
  ConstructiveDilemmaOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt{ℓ₃} → Stmt{ℓ₄} → Stmt
  ConstructiveDilemmaOn(X₁)(X₂)(Y₁)(Y₂) = ((X₁ → X₂) ∧ (Y₁ → Y₂) ∧ (X₁ ∨ Y₁)) → (X₂ ∨ Y₂)
  ConstructiveDilemma = ∀⁴ᶠ(ConstructiveDilemmaOn)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Classical names

module _ {ℓ₁ ℓ₂} where
  ModusTollensOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  ModusTollensOn(X)(Y) = ((X → Y) ∧ (¬ Y)) → (¬ X)
  ModusTollens = ∀²ᶠ(ModusTollensOn)

  ModusPonensOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  ModusPonensOn(X)(Y) = ((X → Y) ∧ X) → Y
  ModusPonens = ∀²ᶠ(ModusPonensOn)

  ReductioAdAbsurdumOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  ReductioAdAbsurdumOn(X)(Y) = ((X → Y) ∧ (X → (¬ Y))) → (¬ X)
  ReductioAdAbsurdum = ∀²ᶠ(ReductioAdAbsurdumOn)

  ReductioAdAbsurdumNegatedOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  ReductioAdAbsurdumNegatedOn(X)(Y) = (((¬ X) → Y) ∧ ((¬ X) → (¬ Y))) → (¬ X)
  ReductioAdAbsurdumNegated = ∀²ᶠ(ReductioAdAbsurdumNegatedOn)
