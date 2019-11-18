module Logic.Names where

open import Logic
open import Logic.Predicate
open import Logic.Propositional

module _ {ℓ} where
  ExcludedMiddleOn : Stmt{ℓ} → Stmt
  ExcludedMiddleOn(X) = (X ∨ (¬ X))
  ExcludedMiddle = ∀ₗ(ExcludedMiddleOn)

  NonContradictionOn : Stmt{ℓ} → Stmt
  NonContradictionOn(X) = ¬(X ∧ (¬ X))
  NonContradiction = ∀ₗ(NonContradictionOn)

  DoubleNegationOn : Stmt{ℓ} → Stmt
  DoubleNegationOn(X) = (¬(¬ X)) → X
  DoubleNegation = ∀ₗ(DoubleNegationOn)

module _ {ℓ₁ ℓ₂} where
  CallCCOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  CallCCOn(X)(Y) = (((X → Y) → X) → X)
  CallCC = ∀²(CallCCOn)

  ContrapositiveOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  ContrapositiveOn(X)(Y) = (X → Y) → ((¬ Y) → (¬ X))
  Contrapositive = ∀²(ContrapositiveOn)

  DisjunctiveSyllogismₗOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  DisjunctiveSyllogismₗOn(X)(Y) = ((X ∨ Y) ∧ (¬ Y)) → X
  DisjunctiveSyllogismₗ = ∀²(DisjunctiveSyllogismₗOn)

  DisjunctiveSyllogismᵣOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  DisjunctiveSyllogismᵣOn(X)(Y) = ((X ∨ Y) ∧ (¬ X)) → Y
  DisjunctiveSyllogismᵣ = ∀²(DisjunctiveSyllogismᵣOn)

  MaterialImplicationOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  MaterialImplicationOn(X)(Y) = (X → Y) ↔ ((¬ X) ∨ Y)
  MaterialImplication = ∀²(MaterialImplicationOn)

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} where
  ConstructiveDilemmaOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt{ℓ₃} → Stmt{ℓ₄} → Stmt
  ConstructiveDilemmaOn(X₁)(X₂)(Y₁)(Y₂) = ((X₁ → X₂) ∧ (Y₁ → Y₂) ∧ (X₁ ∨ Y₁)) → (X₂ ∨ Y₂)
  ConstructiveDilemma = ∀⁴(ConstructiveDilemmaOn)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Classical names

module _ {ℓ₁ ℓ₂} where
  ModusTollensOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  ModusTollensOn(X)(Y) = ((X → Y) ∧ (¬ Y)) → (¬ X)
  ModusTollens = ∀²(ModusTollensOn)

  ModusPonensOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  ModusPonensOn(X)(Y) = ((X → Y) ∧ X) → Y
  ModusPonens = ∀²(ModusPonensOn)

  ReductioAdAbsurdumOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  ReductioAdAbsurdumOn(X)(Y) = ((X → Y) ∧ (X → (¬ Y))) → (¬ X)
  ReductioAdAbsurdum = ∀²(ReductioAdAbsurdumOn)

  ReductioAdAbsurdumNegatedOn : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  ReductioAdAbsurdumNegatedOn(X)(Y) = (((¬ X) → Y) ∧ ((¬ X) → (¬ Y))) → (¬ X)
  ReductioAdAbsurdumNegated = ∀²(ReductioAdAbsurdumNegatedOn)
