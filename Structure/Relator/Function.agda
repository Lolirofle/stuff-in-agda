module Structure.Relator.Function where

import      Lvl
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Functional
open import Structure.Setoid
open import Structure.Setoid.Uniqueness
open import Structure.Relator
open import Type

module _ {ℓₒ₁ ℓₒ₂ ℓₒ₃} {A : Type{ℓₒ₁}}{B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv(B) ⦄ (φ : A → B → Stmt{ℓₒ₃}) where
  module _ (f : A → B) where
    record Computable : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃} where
      constructor intro
      field proof : ∀{x}{y} → (f(x) ≡ y) → φ(x)(y)
    computable = inst-fn Computable.proof

  -- A binary operation is total when every LHS have at least one RHS in which the relation holds.
  record Total : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃} where
    constructor intro
    field proof : ∀{x} → ∃(y ↦ φ(x)(y))

    compute : A → B
    compute(x) = [∃]-witness(proof{x})

    computableFunction : ⦃ _ : ∀{x} → UnaryRelator(φ(x)) ⦄ → ∃(Computable)
    ∃.witness computableFunction = compute
    Computable.proof (∃.proof computableFunction) {x} eq = substitute₁(φ(x)) eq ([∃]-proof(proof{x}))
  total = inst-fn Total.proof

  -- A binary operation is a function when every LHS have at least one RHS in which the relation holds.
  record Function : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃} where
    constructor intro
    field proof : ∀{x} → Unique(φ(x))
  function = inst-fn Function.proof
  -- (∀{x}{y₁ y₂} → φ(x)(y₁) → φ(x)(y₂) → (y₁ ≡ y₂))

  totalFunction : ⦃ _ : Total ⦄ → ⦃ _ : Function ⦄ → (∀{x} → ∃!(φ(x)))
  totalFunction = [∧]-intro total function
