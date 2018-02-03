module Structure.Function {ℓₗ} where

import      Lvl
open import Logic.Propositional
open import Logic.Predicate{ℓₗ}
open import Functional
open import Relator.Equals{ℓₗ}
open import Relator.Equals.Theorems{ℓₗ}
open import Relator.Equals.Uniqueness{ℓₗ}
open import Structure.Function.Domain{ℓₗ}
open import Type

module _ {ℓₒ₁ ℓₒ₂} where
  -- A binary operation is total when every LHS have at least one RHS in which the relation holds.
  Totality : ∀{A : Type{ℓₒ₁}}{B : Type{ℓₒ₂}} → (A → B → Stmt) → Stmt
  Totality{A}{B} (φ) = (∀{x} → ∃(y ↦ φ(x)(y)))

  -- A binary operation is a function when every LHS have at least one RHS in which the relation holds.
  Function : ∀{A : Type{ℓₒ₁}}{B : Type{ℓₒ₂}} → (A → B → Stmt{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂}) → Stmt
  Function{A}{B} (φ) = (∀{x} → Uniqueness{ℓₒ₂}{ℓₒ₁} (φ(x)))
  -- (∀{x}{y₁ y₂} → φ(x)(y₁) → φ(x)(y₂) → (y₁ ≡ y₂))

module _ {ℓₒ₁ ℓₒ₂} where
  function-existence : ∀{A : Type{ℓₒ₁}}{B : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂}} → (φ : A → B → Stmt) → ⦃ _ : Totality(φ)⦄ → ⦃ _ : Function(φ)⦄ → ∃(f ↦ ∀{x}{y} → (f(x) ≡ y) ↔ φ(x)(y))
  function-existence{A}{B} (φ) ⦃ totality ⦄ ⦃ function ⦄ = [∃]-intro(f) ⦃ \{x y} → proof{x}{y} ⦄ where
    f : A → B
    f(x) = [∃]-witness(totality{x})

    proof : ∀{x}{y} → (f(x) ≡ y) ↔ φ(x)(y)
    proof{x}{y} = [↔]-intro l r where
      l : (f(x) ≡ y) ← φ(x)(y)
      l(φxy) = function([∃]-proof(totality{x})) (φxy)
        -- [∃]-proof(totality{x}) ∧ φ(x)(y)
        -- φ(x)([∃]-witness(totality{x})) ∧ φ(x)(y)
        -- [∃]-witness(totality{x}) = y
        -- f(x) = y

      r : (f(x) ≡ y) → φ(x)(y)
      r([≡]-intro) = [∃]-proof(totality{x})
        -- φ(x)(y)
        -- φ(x)([∃]-witness(totality{x}))

  -- Conditions for a binary operation to be a total function.
  function : ∀{A : Type{ℓₒ₁}}{B : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂}} → (φ : A → B → Stmt) → ⦃ _ : Totality(φ)⦄ → ⦃ _ : Function(φ)⦄ → (A → B)
  function(φ) ⦃ totality ⦄ ⦃ function ⦄ = [∃]-witness(function-existence(φ) ⦃ totality ⦄ ⦃ function ⦄)
