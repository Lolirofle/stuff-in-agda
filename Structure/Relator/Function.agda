module Structure.Relator.Function where

import      Lvl
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Functional
open import Sets.Setoid.Uniqueness
open import Relator.Equals.Proofs
open import Type

module _ {ℓₒ₁ ℓₒ₂ ℓₒ₃} {A : Type{ℓₒ₁}}{B : Type{ℓₒ₂}} (φ : A → B → Stmt{ℓₒ₃}) where
  -- A binary operation is total when every LHS have at least one RHS in which the relation holds.
  record FunctionTotal : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃} where
    constructor intro
    field proof : (∀{x} → ∃(y ↦ φ(x)(y)))
  functionTotal = inst-fn FunctionTotal.proof

  -- A binary operation is a function when every LHS have at least one RHS in which the relation holds.
  record Function : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃} where
    constructor intro
    field proof : (∀{x} → Unique(φ(x)))
  function = inst-fn Function.proof
  -- (∀{x}{y₁ y₂} → φ(x)(y₁) → φ(x)(y₂) → (y₁ ≡ y₂))


