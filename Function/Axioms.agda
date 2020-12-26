module Function.Axioms where

import      Function.Names as Names
open import Lang.Instance
open import Logic.Predicate
open import Logic
import      Lvl
open import Structure.Setoid
open import Type

private variable ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ : Lvl.Level

module _
  {A : Type{ℓₒ₁}}
  {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄
  ⦃ _ : Equiv{ℓₗ₃}(A → B) ⦄
  (f g : A → B)
  where

  record FunctionExtensionalityOn : Stmt{ℓₒ₁ Lvl.⊔ ℓₗ₂ Lvl.⊔ ℓₗ₃} where
    constructor intro
    field proof : Names.FunctionExtensionalityOn(f)(g)
  functionExtensionalityOn = inst-fn FunctionExtensionalityOn.proof

  record FunctionApplicationOn : Stmt{ℓₒ₁ Lvl.⊔ ℓₗ₂ Lvl.⊔ ℓₗ₃} where
    constructor intro
    field proof : Names.FunctionApplicationOn(f)(g)
  functionApplicationOn = inst-fn FunctionApplicationOn.proof

module _ (A : Type{ℓₒ₁}) (B : Type{ℓₒ₂}) ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ ⦃ _ : Equiv{ℓₗ₃}(A → B) ⦄ where
  FunctionExtensionality : Stmt
  FunctionExtensionality = ∀²(FunctionExtensionalityOn{ℓₒ₁}{ℓₒ₂}{ℓₗ₂}{ℓₗ₃}{A}{B})
  functionExtensionality : ⦃ funcExt : FunctionExtensionality ⦄ → Names.FunctionExtensionality(A)(B)
  functionExtensionality {f}{g} = functionExtensionalityOn f g

  FunctionApplication : Stmt
  FunctionApplication = ∀²(FunctionApplicationOn{ℓₒ₁}{ℓₒ₂}{ℓₗ₂}{ℓₗ₃}{A}{B})
  functionApplication : ⦃ funcApp : FunctionApplication ⦄ → Names.FunctionApplication(A)(B)
  functionApplication {f}{g} = functionApplicationOn f g

module _
  {A : Type{ℓₒ₁}}
  {B : A → Type{ℓₒ₂}} ⦃ _ : ∀{a} → Equiv{ℓₗ₂}(B(a)) ⦄
  ⦃ _ : Equiv{ℓₗ₃}((a : A) → B(a)) ⦄
  (f g : ((a : A) → B(a)))
  where

  record DependentFunctionExtensionalityOn : Stmt{ℓₒ₁ Lvl.⊔ ℓₗ₂ Lvl.⊔ ℓₗ₃} where
    constructor intro
    field proof : Names.DependentFunctionExtensionalityOn(f)(g)
  dependentFunctionExtensionalityOn = inst-fn DependentFunctionExtensionalityOn.proof

module _ (A : Type{ℓₒ₁}) (B : A → Type{ℓₒ₂}) ⦃ _ : ∀{a} → Equiv{ℓₗ₂}(B(a)) ⦄ ⦃ _ : Equiv{ℓₗ₃}((a : A) → B(a)) ⦄ where
  DependentFunctionExtensionality : Stmt
  DependentFunctionExtensionality = ∀²(DependentFunctionExtensionalityOn{ℓₒ₁}{ℓₒ₂}{ℓₗ₂}{ℓₗ₃}{A}{B})
  dependentFunctionExtensionality : ⦃ depFuncExt : DependentFunctionExtensionality ⦄ → Names.DependentFunctionExtensionality(A)(B)
  dependentFunctionExtensionality {f}{g} = dependentFunctionExtensionalityOn f g

module _
  {A : Type{ℓₒ₁}}
  {B : A → Type{ℓₒ₂}} ⦃ _ : ∀{a} → Equiv{ℓₗ₂}(B(a)) ⦄
  ⦃ _ : Equiv{ℓₗ₃}({a : A} → B(a)) ⦄
  (f g : ({a : A} → B(a)))
  where

  record DependentImplicitFunctionExtensionalityOn : Stmt{ℓₒ₁ Lvl.⊔ ℓₗ₂ Lvl.⊔ ℓₗ₃} where
    constructor intro
    field proof : Names.DependentImplicitFunctionExtensionalityOn(f)(g)
  dependentImplicitFunctionExtensionalityOn = inst-fn DependentImplicitFunctionExtensionalityOn.proof

module _ (A : Type{ℓₒ₁}) (B : A → Type{ℓₒ₂}) ⦃ _ : ∀{a} → Equiv{ℓₗ₂}(B(a)) ⦄ ⦃ _ : Equiv{ℓₗ₃}({a : A} → B(a)) ⦄ where
  DependentImplicitFunctionExtensionality : Stmt
  DependentImplicitFunctionExtensionality = ∀²(DependentImplicitFunctionExtensionalityOn{ℓₒ₁}{ℓₒ₂}{ℓₗ₂}{ℓₗ₃}{A}{B})
  dependentImplicitFunctionExtensionality : ⦃ depFuncExt : DependentImplicitFunctionExtensionality ⦄ → Names.DependentImplicitFunctionExtensionality(A)(B)
  dependentImplicitFunctionExtensionality {f}{g} = dependentImplicitFunctionExtensionalityOn f g

module _
  {A : Type{ℓₒ₁}}
  {B : A → Type{ℓₒ₂}} ⦃ _ : ∀{a} → Equiv{ℓₗ₂}(B(a)) ⦄
  ⦃ _ : Equiv{ℓₗ₃}(⦃ a : A ⦄ → B(a)) ⦄
  (f g : (⦃ a : A ⦄ → B(a)))
  where

  record DependentInstanceFunctionExtensionalityOn : Stmt{ℓₒ₁ Lvl.⊔ ℓₗ₂ Lvl.⊔ ℓₗ₃} where
    constructor intro
    field proof : Names.DependentInstanceFunctionExtensionalityOn(f)(g)
  dependentInstanceFunctionExtensionalityOn = inst-fn DependentInstanceFunctionExtensionalityOn.proof

module _ (A : Type{ℓₒ₁}) (B : A → Type{ℓₒ₂}) ⦃ _ : ∀{a} → Equiv{ℓₗ₂}(B(a)) ⦄ ⦃ _ : Equiv{ℓₗ₃}(⦃ a : A ⦄ → B(a)) ⦄ where
  DependentInstanceFunctionExtensionality : Stmt
  DependentInstanceFunctionExtensionality = ∀²(DependentInstanceFunctionExtensionalityOn{ℓₒ₁}{ℓₒ₂}{ℓₗ₂}{ℓₗ₃}{A}{B})
  dependentInstanceFunctionExtensionality : ⦃ depFuncExt : DependentInstanceFunctionExtensionality ⦄ → Names.DependentInstanceFunctionExtensionality(A)(B)
  dependentInstanceFunctionExtensionality {f}{g} = dependentInstanceFunctionExtensionalityOn f g

