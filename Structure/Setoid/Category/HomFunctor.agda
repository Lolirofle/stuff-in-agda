module Structure.Setoid.Category.HomFunctor where

import      Functional as Fn
open import Function.EqualsRaw
open import Logic.Predicate
import      Lvl
open import Structure.Category
open import Structure.Category.Dual
open import Structure.Category.Functor.Contravariant
open import Structure.Category.Functor
open import Structure.Categorical.Functor.Properties
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Setoid
open import Syntax.Function
open import Syntax.Transitivity
open import Structure.Setoid.Category
open import Type

private variable ℓ ℓₒ ℓₘ ℓₑ : Lvl.Level

module _ (C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}) where
  open CategoryObject(C)
  open Category.ArrowNotation ⦃ … ⦄
  private open module MorphismEquiv {x}{y} = Equivalence (Equiv-equivalence ⦃ morphism-equiv{x}{y} ⦄) using ()

  covariantHomFunctor : Object → (C →ᶠᵘⁿᶜᵗᵒʳ setoidCategoryObject)
  ∃.witness (covariantHomFunctor x) y = [∃]-intro (x ⟶ y)
  Functor.map (∃.proof (covariantHomFunctor _)) f = [∃]-intro (f ∘_) ⦃ BinaryOperator.unary₂ binaryOperator ⦄
  (Function.congruence (Functor.map-function (∃.proof (covariantHomFunctor _))) {f₁} {f₂} f₁f₂) {g} =
    f₁ ∘ g 🝖-[ congruence₂-₁(_∘_) g f₁f₂ ]
    f₂ ∘ g 🝖-end
  Preserving.proof(Functor.op-preserving (∃.proof (covariantHomFunctor _))) {f} {g} {h} =
    (f ∘ g) ∘ h            🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
    f ∘ (g ∘ h)            🝖[ _≡_ ]-[]
    ((f ∘_) Fn.∘ (g ∘_)) h 🝖-end
  Preserving.proof(Functor.id-preserving (∃.proof (covariantHomFunctor _))) {f} =
    id ∘ f   🝖[ _≡_ ]-[ Morphism.identityₗ(_∘_)(id) ]
    f        🝖[ _≡_ ]-[]
    Fn.id(f) 🝖-end

  contravariantHomFunctor : Object → (C →ᶜᵒⁿᵗʳᵃᵛᵃʳⁱᵃⁿᵗᶠᵘⁿᶜᵗᵒʳ setoidCategoryObject)
  ∃.witness (contravariantHomFunctor x) y = [∃]-intro (y ⟶ x)
  Functor.map (∃.proof (contravariantHomFunctor _)) f = [∃]-intro (_∘ f) ⦃ BinaryOperator.unary₁ binaryOperator ⦄
  (Function.congruence (Functor.map-function (∃.proof (contravariantHomFunctor _))) {g₁} {g₂} g₁g₂) {f} =
    f ∘ g₁ 🝖-[ congruence₂-₂(_∘_) f g₁g₂ ]
    f ∘ g₂ 🝖-end
  Preserving.proof(Functor.op-preserving (∃.proof (contravariantHomFunctor _))) {h} {g} {f} =
    f ∘ (g ∘ h)            🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
    (f ∘ g) ∘ h            🝖[ _≡_ ]-[]
    ((_∘ h) Fn.∘ (_∘ g)) f 🝖-end
  Preserving.proof(Functor.id-preserving (∃.proof (contravariantHomFunctor _))) {f} =
    f ∘ id   🝖[ _≡_ ]-[ Morphism.identityᵣ(_∘_)(id) ]
    f        🝖[ _≡_ ]-[]
    Fn.id(f) 🝖-end
