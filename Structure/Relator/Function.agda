module Structure.Relator.Function where

import      Lvl
open import Functional.Instance
open import Logic
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Setoid.Uniqueness
open import Syntax.Function
open import Type

private variable ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₑ₂ : Lvl.Level

module _ {A : Type{ℓₒ₁}}{B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ (φ : A → B → Stmt{ℓₒ₃}) where
  module _ (f : A → B) where
    record Computable : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃ Lvl.⊔ ℓₑ₂} where
      constructor intro
      field proof : ∀{x}{y} → (f(x) ≡ y) → φ(x)(y)
    computable = inferArg Computable.proof

  -- A binary operation is total when every LHS have at least one RHS in which the relation holds.
  record Total : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃} where
    constructor intro
    field proof : ∀{x} → ∃(y ↦ φ(x)(y))

    compute : A → B
    compute(x) = [∃]-witness(proof{x})
  total = inferArg Total.proof

  -- A binary operation is a function when every LHS have at least one RHS in which the relation holds.
  -- (∀{x}{y₁ y₂} → φ(x)(y₁) → φ(x)(y₂) → (y₁ ≡ y₂))
  record Function : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃ Lvl.⊔ ℓₑ₂} where
    constructor intro
    field proof : ∀{x} → Unique(φ(x))
  function = inferArg Function.proof
