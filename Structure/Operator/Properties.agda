module Structure.Operator.Properties where

import      Lvl
open import Functional
open import Lang.Instance
open import Logic
open import Logic.Predicate
import      Structure.Operator.Names as Names
open import Structure.Setoid.WithLvl
open import Syntax.Function
open import Type

private variable ℓ ℓₑ ℓ₁ ℓ₂ ℓ₃ ℓₑ₁ ℓₑ₂ ℓₑ₃ : Lvl.Level

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(T₂) ⦄ (_▫_ : T₁ → T₁ → T₂) where
  record Commutativity : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ₂} where
    constructor intro
    field proof : Names.Commutativity(_▫_)
  commutativity = inst-fn Commutativity.proof

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(T₂) ⦄ (_▫_ : T₁ → T₂ → T₂) (id : T₁) where
  record Identityₗ : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ₂} where
    constructor intro
    field proof : Names.Identityₗ(_▫_)(id)
  identityₗ = inst-fn Identityₗ.proof

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(T₂) ⦄ (_▫_ : T₁ → T₂ → T₂) (null : T₂) where
  record Absorberᵣ : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ₂} where
    constructor intro
    field proof : Names.Absorberᵣ(_▫_)(null)
  absorberᵣ = inst-fn Absorberᵣ.proof

module _ {T₁ : Type{ℓ₁}} ⦃ _ : Equiv{ℓₑ₁}(T₁) ⦄ {T₂ : Type{ℓ₂}} (_▫_ : T₁ → T₂ → T₁) (id : T₂) where
  record Identityᵣ : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ₁} where
    constructor intro
    field proof : Names.Identityᵣ(_▫_)(id)
  identityᵣ = inst-fn Identityᵣ.proof

module _ {T₁ : Type{ℓ₁}} ⦃ _ : Equiv{ℓₑ₁}(T₁) ⦄ {T₂ : Type{ℓ₂}} (_▫_ : T₁ → T₂ → T₁) (null : T₁) where
  record Absorberₗ : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ₁} where
    constructor intro
    field proof : Names.Absorberₗ(_▫_)(null)
  absorberₗ = inst-fn Absorberₗ.proof

module _{T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) (id : T) where
  record Identity : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ} where
    constructor intro
    field
      instance ⦃ left ⦄  : Identityₗ(_▫_)(id)
      instance ⦃ right ⦄ : Identityᵣ(_▫_)(id)
  identity-left = inst-fn (Identityₗ.proof ∘ Identity.left)
  identity-right = inst-fn (Identityᵣ.proof ∘ Identity.right)

module _{T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) where
  record Idempotence : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ} where
    constructor intro
    field proof : Names.Idempotence(_▫_)
  idempotence = inst-fn Idempotence.proof

module _{T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) (id : T) where
  record Absorber : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ} where
    constructor intro
    field
      instance ⦃ left ⦄  : Absorberₗ(_▫_)(id)
      instance ⦃ right ⦄ : Absorberᵣ(_▫_)(id)
  absorber-left = inst-fn (Absorberₗ.proof ∘ Absorber.left)
  absorber-right = inst-fn (Absorberᵣ.proof ∘ Absorber.right)

module _{T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) ⦃ identityₗ : ∃(Identityₗ(_▫_)) ⦄ where
  module _ (inv : T → T) where
    record InverseFunctionₗ : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ} where
      constructor intro
      field proof : Names.InverseFunctionₗ(_▫_)([∃]-witness identityₗ)(inv)
    inverseFunctionₗ = inst-fn InverseFunctionₗ.proof
  Invertibleₗ = ∃(InverseFunctionₗ)

module _{T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) ⦃ identityᵣ : ∃(Identityᵣ(_▫_)) ⦄ where
  module _ (inv : T → T) where
    record InverseFunctionᵣ : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ} where
      constructor intro
      field proof : Names.InverseFunctionᵣ(_▫_)([∃]-witness identityᵣ)(inv)
    inverseFunctionᵣ = inst-fn InverseFunctionᵣ.proof
  Invertibleᵣ = ∃(InverseFunctionᵣ)

module _{T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) ⦃ identity : ∃(Identity(_▫_)) ⦄ where
  module _ (inv : T → T) where
    import Logic.IntroInstances

    record InverseFunction : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ} where
      constructor intro
      field
        instance ⦃ left ⦄  : InverseFunctionₗ(_▫_) ⦃ [∃]-map-proof Identity.left  identity ⦄ (inv)
        instance ⦃ right ⦄ : InverseFunctionᵣ(_▫_) ⦃ [∃]-map-proof Identity.right identity ⦄ (inv)
    inverseFunction-left  = inst-fn (InverseFunctionₗ.proof ∘ InverseFunction.left)
    inverseFunction-right = inst-fn (InverseFunctionᵣ.proof ∘ InverseFunction.right)
  Invertible = ∃(InverseFunction)

module _{T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) ⦃ absorberₗ : ∃(Absorberₗ(_▫_)) ⦄ where
  module _ (opp : T → T) where
    record ComplementFunctionₗ : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ} where
      constructor intro
      field proof : Names.InverseFunctionₗ(_▫_)([∃]-witness absorberₗ)(opp)
    oppositeFunctionₗ = inst-fn ComplementFunctionₗ.proof

module _{T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) ⦃ absorberᵣ : ∃(Absorberᵣ(_▫_)) ⦄ where
  module _ (opp : T → T) where
    record ComplementFunctionᵣ : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ} where
      constructor intro
      field proof : Names.InverseFunctionᵣ(_▫_)([∃]-witness absorberᵣ)(opp)
    oppositeFunctionᵣ = inst-fn ComplementFunctionᵣ.proof

module _{T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) ⦃ absorber : ∃(Absorber(_▫_)) ⦄ where
  module _ (opp : T → T) where
    record ComplementFunction : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ} where
      constructor intro
      field
        instance ⦃ left ⦄  : ComplementFunctionₗ(_▫_) ⦃ [∃]-map-proof Absorber.left  absorber ⦄ (opp)
        instance ⦃ right ⦄ : ComplementFunctionᵣ(_▫_) ⦃ [∃]-map-proof Absorber.right absorber ⦄ (opp)

module _{T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) where
  record Associativity : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ} where
    constructor intro
    field proof : Names.Associativity(_▫_)
  associativity = inst-fn Associativity.proof

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(T₂) ⦄ (_▫₁_ : T₁ → T₂ → T₂) (_▫₂_ : T₂ → T₂ → T₂) where
  record Distributivityₗ : Stmt{Lvl.of(Type.of(_▫₁_)) Lvl.⊔ Lvl.of(Type.of(_▫₂_)) Lvl.⊔ ℓₑ₂} where
    constructor intro
    field proof : Names.Distributivityₗ(_▫₁_)(_▫₂_)
  distributivityₗ = inst-fn Distributivityₗ.proof

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(T₂) ⦄ (_▫₁_ : T₂ → T₁ → T₂) (_▫₂_ : T₂ → T₂ → T₂) where
  record Distributivityᵣ : Stmt{Lvl.of(Type.of(_▫₁_)) Lvl.⊔ Lvl.of(Type.of(_▫₂_)) Lvl.⊔ ℓₑ₂} where
    constructor intro
    field proof : Names.Distributivityᵣ(_▫₁_)(_▫₂_)
  distributivityᵣ = inst-fn Distributivityᵣ.proof

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(T₂) ⦄ {T₃ : Type{ℓ₃}} ⦃ _ : Equiv{ℓₑ₃}(T₃) ⦄ (_▫_ : T₁ → T₂ → T₃) where
  record Cancellationₗ : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ₂ Lvl.⊔ ℓₑ₃} where
    constructor intro
    field proof : Names.Cancellationₗ(_▫_)
  cancellationₗ = inst-fn Cancellationₗ.proof

module _ {T₁ : Type{ℓ₁}} ⦃ _ : Equiv{ℓₑ₁}(T₁) ⦄ {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv{ℓₑ₃}(T₃) ⦄ (_▫_ : T₁ → T₂ → T₃) where
  record Cancellationᵣ : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓₑ₃} where
    constructor intro
    field proof : Names.Cancellationᵣ(_▫_)
  cancellationᵣ = inst-fn Cancellationᵣ.proof

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv{ℓₑ₁}(T₁) ⦄ (_▫₁_ : T₁ → T₃ → T₁) (_▫₂_ : T₁ → T₂ → T₃) where
  record Absorptionₗ : Stmt{Lvl.of(Type.of(_▫₁_)) Lvl.⊔ Lvl.of(Type.of(_▫₂_)) Lvl.⊔ ℓₑ₁} where
    constructor intro
    field proof : Names.Absorptionₗ(_▫₁_)(_▫₂_)
  absorptionₗ = inst-fn Absorptionₗ.proof

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv{ℓₑ₂}(T₂) ⦄ (_▫₁_ : T₃ → T₂ → T₂) (_▫₂_ : T₁ → T₂ → T₃) where
  record Absorptionᵣ : Stmt{Lvl.of(Type.of(_▫₁_)) Lvl.⊔ Lvl.of(Type.of(_▫₂_)) Lvl.⊔ ℓₑ₂} where
    constructor intro
    field proof : Names.Absorptionᵣ(_▫₁_)(_▫₂_)
  absorptionᵣ = inst-fn Absorptionᵣ.proof

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(T₂) ⦄ (_▫_ : T₁ → T₂ → T₂) (inv : T₁ → T₁) where
  record InversePropertyₗ : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ₂} where
    constructor intro
    field proof : Names.InversePropertyₗ(_▫_)(inv)
  inversePropₗ = inst-fn InversePropertyₗ.proof

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(T₂) ⦄ (_▫_ : T₂ → T₁ → T₂) (inv : T₁ → T₁) where
  record InversePropertyᵣ : Stmt{Lvl.of(Type.of(_▫_)) Lvl.⊔ ℓₑ₂} where
    constructor intro
    field proof : Names.InversePropertyᵣ(_▫_)(inv)
  inversePropᵣ = inst-fn InversePropertyᵣ.proof

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv{ℓₑ₃}(T₃) ⦄ (_▫₁_ : T₁ → T₂ → T₃) (_▫₂_ : T₁ → T₃ → T₂) where
  record InverseOperatorₗ : Stmt{Lvl.of(Type.of(_▫₁_)) Lvl.⊔ Lvl.of(Type.of(_▫₂_)) Lvl.⊔ ℓₑ₃} where
    constructor intro
    field proof : Names.InverseOperatorₗ(_▫₁_)(_▫₂_)
  inverseOperₗ = inst-fn InverseOperatorₗ.proof

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv{ℓₑ₃}(T₃) ⦄ (_▫₁_ : T₁ → T₂ → T₃) (_▫₂_ : T₃ → T₂ → T₁) where
  record InverseOperatorᵣ : Stmt{Lvl.of(Type.of(_▫₁_)) Lvl.⊔ Lvl.of(Type.of(_▫₂_)) Lvl.⊔ ℓₑ₃} where
    constructor intro
    field proof : Names.InverseOperatorᵣ(_▫₁_)(_▫₂_)
  inverseOperᵣ = inst-fn InverseOperatorᵣ.proof
