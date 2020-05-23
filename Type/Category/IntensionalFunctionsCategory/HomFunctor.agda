module Type.Category.IntensionalFunctionsCategory.HomFunctor where

import      Functional as Fn
open import Function.Proofs
open import Logic.Predicate
import      Lvl
open import Relator.Equals
open import Relator.Equals.Proofs
import      Relator.Equals.Proofs.Equiv
open import Structure.Category
open import Structure.Category.Dual
open import Structure.Category.Functor
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Transitivity
open import Type.Category.IntensionalFunctionsCategory
open import Type

private variable ℓ ℓₒ ℓₘ ℓₑ : Lvl.Level

module _
  {Obj : Type{ℓₒ}}
  {_⟶_ : Obj → Obj → Type{ℓₘ}}
  (C : Category(_⟶_))
  where

  open Category(C)

  covariantHomFunctor : Obj → (intro(C) →ᶠᵘⁿᶜᵗᵒʳ typeIntensionalFnCategoryObject{ℓₘ})
  ∃.witness (covariantHomFunctor x) y = (x ⟶ y)
  Functor.map (∃.proof (covariantHomFunctor _)) = (_∘_)
  Function.congruence (Functor.map-function (∃.proof (covariantHomFunctor _))) = congruence₁(_∘_)
  Functor.op-preserving (∃.proof (covariantHomFunctor x)) {f = f} {g = g} =
    (h ↦ (f ∘ g) ∘ h)  🝖[ _≡_ ]-[ {!!} ] -- TODO: Requires func. ext?
    (h ↦ f ∘ (g ∘ h))  🝖[ _≡_ ]-[]
    (f ∘_) Fn.∘ (g ∘_) 🝖-end
  Functor.id-preserving (∃.proof (covariantHomFunctor x)) = {!!}
{-
  contravariantHomFunctor : Object → (dual(C) →ᶠᵘⁿᶜᵗᵒʳ typeIntensionalFnCategoryObject{ℓₘ})
  ∃.witness (contravariantHomFunctor x) y = (y ⟶ x)
  Functor.map (∃.proof (contravariantHomFunctor _)) = Fn.swap(_∘_)
  Function.congruence (Functor.map-function (∃.proof (contravariantHomFunctor x))) x₁ = {!!}
  _⊜_.proof (Functor.op-preserving (∃.proof (contravariantHomFunctor x))) {x₁} = {!!}
  _⊜_.proof (Functor.id-preserving (∃.proof (contravariantHomFunctor x))) {x₁} = {!!}
-}
