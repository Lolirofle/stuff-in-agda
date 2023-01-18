module Type.Dependent.PiFunction.Category where

import      DependentFunctional as Fn
open import Logic.Propositional
import      Lvl
open import Structure.Categorical.Properties
open import Structure.Category
open import Structure.Operator
open import Structure.Setoid
open import Type.Dependent.PiFunction
open import Type.Dependent.PiFunction.Equivalence
open import Type

private variable ℓ ℓᵢ ℓₒ ℓₘ ℓₑ ℓₒ₁ ℓₘ₁ ℓₑ₁ ℓₒ₂ ℓₘ₂ ℓₑ₂ : Lvl.Level
private variable I : Type{ℓ}

module _
  {I : Type{ℓᵢ}}
  {Obj : I → Type{ℓₒ}}
  {Morphism : (i : I) → Obj(i) → Obj(i) → Type{ℓₘ}}
  ⦃ morphism-equiv : ∀{i : I}{x y : Obj(i)} → Equiv{ℓₑ}(Morphism(i) x y) ⦄
  (C : (i : I) → Category{Obj = Obj(i)} (Morphism(i)) ⦃ \{x y} → morphism-equiv{i}{x}{y} ⦄)
  where

  private open module CategoryC {i} = Category(C(i))

  productCategory : Category{Obj = Π I Obj} (\x y → Π I \i → Morphism(i) (x(i)) (y(i))) ⦃ product-equiv ⦄
  Category._∘_ productCategory = Fn.pointwise₂,₁(_∘_)
  Category.id  productCategory = \_ → id
  Category.binaryOperator productCategory = intro \p₁ p₂ → congruence₂(_∘_) ⦃ binaryOperator ⦄ p₁ p₂
  Category.associativity  productCategory = Morphism.intro (Morphism.associativity(_∘_) ⦃ associativity ⦄)
  Category.identity       productCategory = [∧]-intro
    (Morphism.intro(Morphism.identityₗ(_∘_)(id) ⦃ identityₗ ⦄))
    (Morphism.intro(Morphism.identityᵣ(_∘_)(id) ⦃ identityᵣ ⦄))

Πᶜᵃᵗ : (I : Type{ℓᵢ}) → (I → CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}) → CategoryObject
Πᶜᵃᵗ I C =
  let open module CatC i = CategoryObject(C(i))
  in intro ⦃ _ ⦄ (productCategory{I = I}{Obj = Object}{Morphism = Morphism} ⦃ \{i} → morphism-equiv i ⦄ category)
