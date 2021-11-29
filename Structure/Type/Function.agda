module Structure.Type.Function where

open import BidirectionalFunction using (_↔_ ; _$ₗ_ ; _$ᵣ_ ; intro)
open import Function as Fn using (_→ᶠ_)
open import Function.Equals
import      Lvl
open import Relator.Equals.Proofs.Equiv
open import Type
open import Structure.Function.Domain
open import Structure.Setoid

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

module _ where
  private variable A : Type{ℓ}
  private variable B : A → Type{ℓ}

  record DependentFunctionType(_⟶_ : (A : Type{ℓ₁}) → (A → Type{ℓ₂}) → Type{ℓ₃}) ⦃ equiv : ∀{A : Type{ℓ₁}}{B : A → Type{ℓ₂}} → Equiv{ℓₑ}(A ⟶ B) ⦄ : Type{Lvl.𝐒(ℓ₁ Lvl.⊔ ℓ₂) Lvl.⊔ ℓ₃ Lvl.⊔ ℓₑ} where
    field
      convert : ((a : A) → B(a)) ↔ (A ⟶ B)
      correctness : InversePair ⦃ Dependent.[⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄ ⦃ equiv{A}{B} ⦄ convert

    _$_ : (A ⟶ B) → (a : A) → B(a)
    _$_ = convert $ₗ_

    lift : ((a : A) → B(a)) → (A ⟶ B)
    lift = convert $ᵣ_

module _ where
  private variable A B C : Type{ℓ}

  -- A type isomorphic to the function type, allowing "application" and "abstraction".
  record FunctionType(_⟶_ : Type{ℓ₁} → Type{ℓ₂} → Type{ℓ₃}) ⦃ equiv : ∀{A : Type{ℓ₁}}{B : Type{ℓ₂}} → Equiv{ℓₑ}(A ⟶ B) ⦄ : Type{Lvl.𝐒(ℓ₁ Lvl.⊔ ℓ₂) Lvl.⊔ ℓ₃ Lvl.⊔ ℓₑ} where
    field
      convert : (A → B) ↔ (A ⟶ B)
      correctness : InversePair ⦃ Dependent.[⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄ ⦃ equiv{A}{B} ⦄ convert

    -- Function application.
    _$_ : (A ⟶ B) → A → B
    _$_ = convert $ₗ_

    -- Function abstraction.
    lift : (A → B) → (A ⟶ B)
    lift = convert $ᵣ_

    -- Constant function.
    const : B → (A ⟶ B)
    const b = lift(Fn.const b)

  open FunctionType ⦃ … ⦄ hiding (convert ; correctness) public

  import      Functional as Fn
  open import Relator.Equals

  instance
    explicit-functionType : FunctionType{ℓ₁}{ℓ₂}(_→ᶠ_)
    FunctionType.convert explicit-functionType = intro(Fn._$_) Fn.id
    Inverseᵣ.proof (InversePair.left  (FunctionType.correctness explicit-functionType)) = [≡]-intro
    Inverseᵣ.proof (InversePair.right (FunctionType.correctness explicit-functionType)) = intro [≡]-intro

  open import Functional.Implicit as Implicit
  instance
    implicit-functionType : FunctionType{ℓ₁}{ℓ₂}(_﹛→﹜_)
    FunctionType.convert implicit-functionType = intro(_﹛$﹜_) Implicit.inferArg
    Inverseᵣ.proof (InversePair.left  (FunctionType.correctness implicit-functionType)) = [≡]-intro
    Inverseᵣ.proof (InversePair.right (FunctionType.correctness implicit-functionType)) = intro [≡]-intro

  open import Functional.Instance as Instance
  instance
    instance-functionType : FunctionType{ℓ₁}{ℓ₂}(_⦃→⦄_)
    FunctionType.convert instance-functionType = intro(_⦃$⦄_) Instance.inferArg
    Inverseᵣ.proof (InversePair.left  (FunctionType.correctness instance-functionType)) = [≡]-intro
    Inverseᵣ.proof (InversePair.right (FunctionType.correctness instance-functionType)) = intro [≡]-intro
