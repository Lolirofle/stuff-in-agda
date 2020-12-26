module Type.Category.ExtensionalFunctionsCategory.HomFunctor where

import      Functional as Fn
open import Function.Proofs
open import Function.Equals
open import Function.Equals.Proofs
open import Logic.Predicate
import      Lvl
import      Relator.Equals.Proofs.Equiv
open import Structure.Category
open import Structure.Category.Dual
open import Structure.Category.Functor
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type.Category.ExtensionalFunctionsCategory
open import Type

private variable ℓ ℓₒ ℓₘ ℓₑ : Lvl.Level

-- Note: This is implicitly using the identity type as the equivalence for (_⟶_).
module _ {Obj : Type{ℓₒ}} {_⟶_ : Obj → Obj → Type{ℓₘ}} (C : Category(_⟶_)) where
  open Category(C)

  covariantHomFunctor : Obj → ((intro C) →ᶠᵘⁿᶜᵗᵒʳ typeExtensionalFnCategoryObject{ℓₘ})
  ∃.witness (covariantHomFunctor x) y = (x ⟶ y)
  Functor.map (∃.proof (covariantHomFunctor _)) = (_∘_)
  _⊜_.proof (Function.congruence (Functor.map-function (∃.proof (covariantHomFunctor _))) {f₁} {f₂} f₁f₂) {g} = congruence₂ₗ(_∘_) ⦃ binaryOperator ⦄ g f₁f₂
  _⊜_.proof (Functor.op-preserving (∃.proof (covariantHomFunctor _))) = Morphism.associativity(_∘_)
  _⊜_.proof (Functor.id-preserving (∃.proof (covariantHomFunctor _))) = Morphism.identityₗ(_∘_)(id)

  contravariantHomFunctor : Obj → (dual(intro C) →ᶠᵘⁿᶜᵗᵒʳ typeExtensionalFnCategoryObject{ℓₘ})
  ∃.witness (contravariantHomFunctor x) y = (y ⟶ x)
  Functor.map (∃.proof (contravariantHomFunctor _)) = Fn.swap(_∘_)
  _⊜_.proof (Function.congruence (Functor.map-function (∃.proof (contravariantHomFunctor _))) {g₁} {g₂} g₁g₂) {f} = congruence₂ᵣ(_∘_) ⦃ binaryOperator ⦄ f g₁g₂
  _⊜_.proof (Functor.op-preserving (∃.proof (contravariantHomFunctor _))) = symmetry(_) (Morphism.associativity(_∘_))
  _⊜_.proof (Functor.id-preserving (∃.proof (contravariantHomFunctor _))) = Morphism.identityᵣ(_∘_)(id)
