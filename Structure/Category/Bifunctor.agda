module Structure.Category.Bifunctor where

import      Lvl
open import Data.Tuple as Tuple using (_,_ ; _⨯_)
open import Data.Tuple.Category
open import Data.Tuple.Equivalence
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Function
open import Structure.Operator
open import Structure.Setoid
open import Type

private variable ℓ ℓₒ ℓₘ ℓₑ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₘ₁ ℓₘ₂ ℓₘ₃ ℓₑ₁ ℓₑ₂ ℓₑ₃ : Lvl.Level
private variable Objₗ Objᵣ Obj₁ Obj₂ Obj₃ : Type{ℓ}
private variable _⟶₁_ _⟶₂_ _⟶₃_ : Objₗ → Objᵣ → Type{ℓ}

module _
  ⦃ morphism-equiv₁ : ∀{x y : Obj₁} → Equiv{ℓₑ₁}(x ⟶₁ y) ⦄
  ⦃ morphism-equiv₂ : ∀{x y : Obj₂} → Equiv{ℓₑ₂}(x ⟶₂ y) ⦄
  ⦃ morphism-equiv₃ : ∀{x y : Obj₃} → Equiv{ℓₑ₃}(x ⟶₃ y) ⦄
  where

  module _
    (A : Category(_⟶₁_))
    (B : Category(_⟶₂_))
    (C : Category(_⟶₃_))
    (F : Obj₁ → Obj₂ → Obj₃)
    where

    Bifunctor = Functor(tupleCategory A B) C (Tuple.uncurry F)

  module Bifunctor
    {A : Category(_⟶₁_)}
    {B : Category(_⟶₂_)}
    {C : Category(_⟶₃_)}
    {F : Obj₁ → Obj₂ → Obj₃}
    (bifunctor : Bifunctor A B C F)
    where

    open Functor(bifunctor)

    bimap : ∀{x₁ y₁ : Obj₁}{x₂ y₂ : Obj₂} → (x₁ ⟶₁ y₁) → (x₂ ⟶₂ y₂) → (F x₁ x₂ ⟶₃ F y₁ y₂)
    bimap = Tuple.curry map

    instance
      bimap-function : ∀{x₁ y₁}{x₂ y₂} → BinaryOperator(bimap{x₁}{y₁}{x₂}{y₂})
      bimap-function = intro(Tuple.curry(congruence₁(map)))

[_,_]→ᵇⁱᶠᵘⁿᶜᵗᵒʳ_ : CategoryObject{ℓₒ₁}{ℓₘ₁}{ℓₑ₁} → CategoryObject{ℓₒ₂}{ℓₘ₂}{ℓₑ₂} → CategoryObject{ℓₒ₃}{ℓₘ₃}{ℓₑ₃} → Type
[ A , B ]→ᵇⁱᶠᵘⁿᶜᵗᵒʳ C = ∃(Bifunctor(CategoryObject.category(A)) (CategoryObject.category(B)) (CategoryObject.category(C)))
