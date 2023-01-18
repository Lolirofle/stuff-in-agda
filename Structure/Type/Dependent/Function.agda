module Structure.Type.Dependent.Function where

open import BidirectionalFunction using (_↔_ ; _$ₗ_ ; _$ᵣ_ ; intro)
open import Function.Equals
import      Lvl
open import Relator.Equals.Proofs.Equiv
open import Type
open import Structure.Function.Domain
open import Structure.Setoid

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓₑ : Lvl.Level
private variable A : Type{ℓ}
private variable B : A → Type{ℓ}

record FunctionType(_⟶_ : (A : Type{ℓ₁}) → (A → Type{ℓ₂}) → Type{ℓ₃}) ⦃ equiv : ∀{A : Type{ℓ₁}}{B : A → Type{ℓ₂}} → Equiv{ℓₑ}(A ⟶ B) ⦄ : Type{Lvl.𝐒(ℓ₁ Lvl.⊔ ℓ₂) Lvl.⊔ ℓ₃ Lvl.⊔ ℓₑ} where
  field
    convert : ((a : A) → B(a)) ↔ (A ⟶ B)
    correctness : InversePair ⦃ Dependent.[⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄ ⦃ equiv{A}{B} ⦄ convert

  -- Function application.
  _$_ : (A ⟶ B) → (a : A) → B(a)
  _$_ = convert $ₗ_

  -- Function abstraction.
  lift : ((a : A) → B(a)) → (A ⟶ B)
  lift = convert $ᵣ_
open FunctionType ⦃ … ⦄ hiding (convert ; correctness) public

open import DependentFunction
open import DependentFunctional as Fn
open import Functional using (id)
open import Relator.Equals

instance
  explicit-functionType : FunctionType{ℓ₁}{ℓ₂}(_→ᶠ_)
  FunctionType.convert explicit-functionType = intro(Fn._$_) id
  Inverseᵣ.proof (InversePair.left  (FunctionType.correctness explicit-functionType)) = [≡]-intro
  Inverseᵣ.proof (InversePair.right (FunctionType.correctness explicit-functionType)) = Dependent.intro [≡]-intro
