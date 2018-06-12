module Logic.Propositional.Names{ℓ} where

open import Logic.Propositional{ℓ}

ExcludedMiddle = (∀{X : Stmt} → (X ∨ (¬ X)))

NonContradiction = (∀{X : Stmt} → ¬(X ∧ (¬ X)))

CallCC = (∀{X Y : Stmt} → (((X → Y) → X) → X))

DoubleNegation = (∀{X : Stmt} → (¬(¬ X)) → X)

Contrapositive = (∀{X Y : Stmt} → (X → Y) → ((¬ Y) → (¬ X)))

DisjunctiveSyllogismₗ = (∀{X Y : Stmt} → ((X ∨ Y) ∧ (¬ Y)) → X)

DisjunctiveSyllogismᵣ = (∀{X Y : Stmt} → ((X ∨ Y) ∧ (¬ X)) → Y)

ConstructiveDilemma = (∀{X₁ X₂ Y₁ Y₂ : Stmt} → ((X₁ → X₂) ∧ (Y₁ → Y₂) ∧ (X₁ ∨ Y₁)) → (X₂ ∨ Y₂))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Classical names

ModusTollens = (∀{X Y : Stmt} → ((X → Y) ∧ (¬ Y)) → (¬ X))

ModusPonens = (∀{X Y : Stmt} → ((X → Y) ∧ X) → Y)

ReductioAdAbsurdum = (∀{X Y : Stmt} → ((X → Y) ∧ (X → (¬ Y))) → (¬ X))

ReductioAdAbsurdumNegated = (∀{X Y : Stmt} → (((¬ X) → Y) ∧ ((¬ X) → (¬ Y))) → (¬ X))
