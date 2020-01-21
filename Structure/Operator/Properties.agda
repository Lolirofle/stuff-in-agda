module Structure.Operator.Properties where

import      Lvl
open import Functional
open import Lang.Instance
open import Logic
open import Logic.Predicate
import      Structure.Operator.Names as Names
open import Sets.Setoid
open import Syntax.Function
open import Type

module _ {ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv(T₂) ⦄ (_▫_ : T₁ → T₁ → T₂) where
  record Commutativity : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Commutativity(_▫_)
  commutativity = inst-fn Commutativity.proof

module _ {ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv(T₂) ⦄ (_▫_ : T₁ → T₂ → T₂) (id : T₁) where
  record Identityₗ : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Identityₗ(_▫_)(id)
  identityₗ = inst-fn Identityₗ.proof

module _ {ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv(T₂) ⦄ (_▫_ : T₁ → T₂ → T₂) (null : T₂) where
  record Absorberᵣ : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Absorberᵣ(_▫_)(null)
  absorberᵣ = inst-fn Absorberᵣ.proof

module _ {ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}} ⦃ _ : Equiv(T₁) ⦄ {T₂ : Type{ℓ₂}} (_▫_ : T₁ → T₂ → T₁) (id : T₂) where
  record Identityᵣ : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Identityᵣ(_▫_)(id)
  identityᵣ = inst-fn Identityᵣ.proof

module _ {ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}} ⦃ _ : Equiv(T₁) ⦄ {T₂ : Type{ℓ₂}} (_▫_ : T₁ → T₂ → T₁) (null : T₁) where
  record Absorberₗ : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Absorberₗ(_▫_)(null)
  absorberₗ = inst-fn Absorberₗ.proof

module _ {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) (id : T) where
  record Identity : Stmt{ℓ} where
    constructor intro
    field
      instance ⦃ left ⦄  : Identityₗ(_▫_)(id)
      instance ⦃ right ⦄ : Identityᵣ(_▫_)(id)
  identity-left = inst-fn (Identityₗ.proof ∘ Identity.left)
  identity-right = inst-fn (Identityᵣ.proof ∘ Identity.right)

module _ {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) where
  record Idempotence : Stmt{ℓ} where
    constructor intro
    field proof : Names.Idempotence(_▫_)
  idempotence = inst-fn Idempotence.proof

module _ {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) (id : T) where
  record Absorber : Stmt{ℓ} where
    constructor intro
    field
      instance ⦃ left ⦄  : Absorberₗ(_▫_)(id)
      instance ⦃ right ⦄ : Absorberᵣ(_▫_)(id)
  absorber-left = inst-fn (Absorberₗ.proof ∘ Absorber.left)
  absorber-right = inst-fn (Absorberᵣ.proof ∘ Absorber.right)

module _ {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) ⦃ identityₗ : ∃(Identityₗ(_▫_)) ⦄ where
  module _ (inv : T → T) where
    record InverseFunctionₗ : Stmt{ℓ} where
      constructor intro
      field proof : Names.InverseFunctionₗ(_▫_)([∃]-witness identityₗ)(inv)
    inverseFunctionₗ = inst-fn InverseFunctionₗ.proof
  Invertibleₗ = ∃(InverseFunctionₗ)

module _ {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) ⦃ identityᵣ : ∃(Identityᵣ(_▫_)) ⦄ where
  module _ (inv : T → T) where
    record InverseFunctionᵣ : Stmt{ℓ} where
      constructor intro
      field proof : Names.InverseFunctionᵣ(_▫_)([∃]-witness identityᵣ)(inv)
    inverseFunctionᵣ = inst-fn InverseFunctionᵣ.proof
  Invertibleᵣ = ∃(InverseFunctionᵣ)

module _ {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) ⦃ identity : ∃(Identity(_▫_)) ⦄ where
  module _ (inv : T → T) where
    record InverseFunction : Stmt{ℓ} where
      constructor intro
      field
        instance ⦃ left ⦄  : InverseFunctionₗ(_▫_) ⦃ [∃]-map-proof Identity.left  identity ⦄ (inv)
        instance ⦃ right ⦄ : InverseFunctionᵣ(_▫_) ⦃ [∃]-map-proof Identity.right identity ⦄ (inv)
    inverseFunction-left = inst-fn (InverseFunctionₗ.proof ∘ InverseFunction.left)
    inverseFunction-right = inst-fn (InverseFunctionᵣ.proof ∘ InverseFunction.right)
  Invertible = ∃(InverseFunction)

-- TODO: Maybe rename to ComplementFunction?
module _ {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) ⦃ absorberₗ : ∃(Absorberₗ(_▫_)) ⦄ where
  module _ (opp : T → T) where
    record OppositeFunctionₗ : Stmt{ℓ} where
      constructor intro
      field proof : Names.InverseFunctionₗ(_▫_)([∃]-witness absorberₗ)(opp)
    oppositeFunctionₗ = inst-fn OppositeFunctionₗ.proof

module _ {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) ⦃ absorberᵣ : ∃(Absorberᵣ(_▫_)) ⦄ where
  module _ (opp : T → T) where
    record OppositeFunctionᵣ : Stmt{ℓ} where
      constructor intro
      field proof : Names.InverseFunctionᵣ(_▫_)([∃]-witness absorberᵣ)(opp)
    oppositeFunctionᵣ = inst-fn OppositeFunctionᵣ.proof

module _ {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) ⦃ absorber : ∃(Absorber(_▫_)) ⦄ where
  module _ (opp : T → T) where
    record OppositeFunction : Stmt{ℓ} where
      constructor intro
      field
        instance ⦃ left ⦄  : OppositeFunctionₗ(_▫_) ⦃ [∃]-map-proof Absorber.left  absorber ⦄ (opp)
        instance ⦃ right ⦄ : OppositeFunctionᵣ(_▫_) ⦃ [∃]-map-proof Absorber.right absorber ⦄ (opp)

module _ {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) where
  record Associativity : Stmt{ℓ} where
    constructor intro
    field proof : Names.Associativity(_▫_)
  associativity = inst-fn Associativity.proof

module _ {ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv(T₂) ⦄ (_▫₁_ : T₁ → T₂ → T₂) (_▫₂_ : T₂ → T₂ → T₂) where
  record Distributivityₗ : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Distributivityₗ(_▫₁_)(_▫₂_)
  distributivityₗ = inst-fn Distributivityₗ.proof

module _ {ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv(T₂) ⦄ (_▫₁_ : T₂ → T₁ → T₂) (_▫₂_ : T₂ → T₂ → T₂) where
  record Distributivityᵣ : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Distributivityᵣ(_▫₁_)(_▫₂_)
  distributivityᵣ = inst-fn Distributivityᵣ.proof

module _ {ℓ₁ ℓ₂ ℓ₃} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv(T₂) ⦄ {T₃ : Type{ℓ₃}} ⦃ _ : Equiv(T₃) ⦄ (_▫_ : T₁ → T₂ → T₃) where
  record Cancellationₗ : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    constructor intro
    field proof : Names.Cancellationₗ(_▫_)
  cancellationₗ = inst-fn Cancellationₗ.proof

module _ {ℓ₁ ℓ₂ ℓ₃} {T₁ : Type{ℓ₁}} ⦃ _ : Equiv(T₁) ⦄ {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv(T₃) ⦄ (_▫_ : T₁ → T₂ → T₃) where
  record Cancellationᵣ : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    constructor intro
    field proof : Names.Cancellationᵣ(_▫_)
  cancellationᵣ = inst-fn Cancellationᵣ.proof

module _ {ℓ₁ ℓ₂ ℓ₃} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv(T₁) ⦄ (_▫₁_ : T₁ → T₃ → T₁) (_▫₂_ : T₁ → T₂ → T₃) where
  record Absorptionₗ : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    constructor intro
    field proof : Names.Absorptionₗ(_▫₁_)(_▫₂_)
  absorptionₗ = inst-fn Absorptionₗ.proof

module _ {ℓ₁ ℓ₂ ℓ₃} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv(T₂) ⦄ (_▫₁_ : T₃ → T₂ → T₂) (_▫₂_ : T₁ → T₂ → T₃) where
  record Absorptionᵣ : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    constructor intro
    field proof : Names.Absorptionᵣ(_▫₁_)(_▫₂_)
  absorptionᵣ = inst-fn Absorptionᵣ.proof
