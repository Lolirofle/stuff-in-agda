module Structure.Category.Functor.Functors where

import      Functional as Fn
open import Function.Proofs
open import Logic.Predicate
import      Lvl
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₒ ℓₘ ℓₑ ℓₗₑ ℓᵣₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ : Lvl.Level
private variable Obj Obj₁ Obj₂ Obj₃ : Type{ℓ}
private variable Morphism Morphism₁ Morphism₂ Morphism₃ : Obj → Obj → Type{ℓ}

module Raw where
  constᶠᵘⁿᶜᵗᵒʳ : Obj₂ → (Obj₁ → Obj₂)
  constᶠᵘⁿᶜᵗᵒʳ = Fn.const

  idᶠᵘⁿᶜᵗᵒʳ : Obj → Obj
  idᶠᵘⁿᶜᵗᵒʳ = Fn.id

  _∘ᶠᵘⁿᶜᵗᵒʳ_ : (Obj₂ → Obj₃) → (Obj₁ → Obj₂) → (Obj₁ → Obj₃)
  _∘ᶠᵘⁿᶜᵗᵒʳ_ = Fn._∘_

  infixl 10000 _∘ᶠᵘⁿᶜᵗᵒʳ_

module _
  ⦃ morphism-equivₗ : ∀{x y : Obj₁} → Equiv{ℓₗₑ}(Morphism₁ x y) ⦄
  ⦃ morphism-equivᵣ : ∀{x y : Obj₂} → Equiv{ℓᵣₑ}(Morphism₂ x y) ⦄
  {Category₁ : Category(Morphism₁)}
  {Category₂ : Category(Morphism₂)}
  where

  module _ where
    private open module Equivₗ {x}{y} = Equivalence (Equiv-equivalence ⦃ morphism-equivₗ{x}{y} ⦄) using ()
    private open module Equivᵣ {x}{y} = Equivalence (Equiv-equivalence ⦃ morphism-equivᵣ{x}{y} ⦄) using ()
    open Category ⦃ … ⦄
    open Functor
    open Raw

    private instance _ = Category₁
    private instance _ = Category₂

    -- A constant functor maps every object and morphism in a category to a single specified object and the identity morphism.
    constant : (objᵣ : Obj₂) → Functor(Category₁)(Category₂)(constᶠᵘⁿᶜᵗᵒʳ(objᵣ))
    map           (constant(objᵣ)) = Fn.const(id)
    op-preserving (constant(objᵣ)) = symmetry(_≡_) (Morphism.identityₗ(_∘_)(id))
    id-preserving (constant(objᵣ)) = reflexivity(_≡_)

module _
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv{ℓₑ}(Morphism x y) ⦄
  {Category : Category(Morphism)}
  where

  private open module [≡]-Equivalence {x}{y} = Equivalence (Equiv-equivalence ⦃ morphism-equiv{x}{y} ⦄) using ()
  open Functor
  open Raw

  private instance _ = Category

  identity : Endofunctor(Category)(idᶠᵘⁿᶜᵗᵒʳ)
  map           (identity) = Fn.id
  op-preserving (identity) = reflexivity(_≡_)
  id-preserving (identity) = reflexivity(_≡_)

module _
  ⦃ morphism-equiv₁ : ∀{x y : Obj₁} → Equiv{ℓₑ₁}(Morphism₁ x y) ⦄
  ⦃ morphism-equiv₂ : ∀{x y : Obj₂} → Equiv{ℓₑ₂}(Morphism₂ x y) ⦄
  ⦃ morphism-equiv₃ : ∀{x y : Obj₃} → Equiv{ℓₑ₃}(Morphism₃ x y) ⦄
  {Category₁ : Category(Morphism₁)}
  {Category₂ : Category(Morphism₂)}
  {Category₃ : Category(Morphism₃)}
  where

  private open module Equiv₃ {x}{y} = Equivalence (Equiv-equivalence ⦃ morphism-equiv₃{x}{y} ⦄) using ()
  open Category ⦃ … ⦄
  open Functor
  open Raw

  private instance _ = Category₁
  private instance _ = Category₂
  private instance _ = Category₃

  composition :
    ∀{F₂₃}{F₁₂}
    → (functor₂₃ : Functor(Category₂)(Category₃)(F₂₃))
    → (functor₁₂ : Functor(Category₁)(Category₂)(F₁₂))
    → Functor(Category₁)(Category₃)(F₂₃ ∘ᶠᵘⁿᶜᵗᵒʳ F₁₂)

  map              (composition{F₂₃}{F₁₂}(functor₂₃)(functor₁₂)){x}{y} = (map(functor₂₃){F₁₂(x)}{F₁₂(y)}) Fn.∘ (map(functor₁₂){x}{y})
  map-function     (composition{F₂₃}{F₁₂}(functor₂₃)(functor₁₂)) = [∘]-function ⦃ func-f = map-function(functor₂₃) ⦄ ⦃ func-g = map-function(functor₁₂) ⦄
  op-preserving    (composition{F₂₃}{F₁₂}(functor₂₃)(functor₁₂)){x}{y}{z} {f}{g} =
    map(functor₂₃) (map(functor₁₂) (f ∘ g))                               🝖-[ congruence₁(map(functor₂₃)) (op-preserving(functor₁₂)) ]
    map(functor₂₃) (map(functor₁₂) f ∘ map functor₁₂ g)                   🝖-[ op-preserving(functor₂₃)]
    map(functor₂₃) (map(functor₁₂) f) ∘ map(functor₂₃) (map(functor₁₂) g) 🝖-end
  id-preserving    (composition{F₂₃}{F₁₂}(functor₂₃)(functor₁₂)) {x} =
    map(functor₂₃) (map(functor₁₂) id) 🝖-[ congruence₁(_) (id-preserving(functor₁₂)) ]
    map(functor₂₃) id                  🝖-[ id-preserving(functor₂₃) ]
    id                                 🝖-end

module Wrapped where
  open CategoryObject

  private variable A B C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}

  constᶠᵘⁿᶜᵗᵒʳ : let _ = A in Object(B) → (A →ᶠᵘⁿᶜᵗᵒʳ B)
  ∃.witness (constᶠᵘⁿᶜᵗᵒʳ c) = Raw.constᶠᵘⁿᶜᵗᵒʳ c
  ∃.proof   (constᶠᵘⁿᶜᵗᵒʳ c) = constant c

  idᶠᵘⁿᶜᵗᵒʳ : A →ᶠᵘⁿᶜᵗᵒʳ A
  ∃.witness idᶠᵘⁿᶜᵗᵒʳ = Raw.idᶠᵘⁿᶜᵗᵒʳ
  ∃.proof   idᶠᵘⁿᶜᵗᵒʳ = identity

  _∘ᶠᵘⁿᶜᵗᵒʳ_ : let _ = A ; _ = B ; _ = C in (B →ᶠᵘⁿᶜᵗᵒʳ C) → (A →ᶠᵘⁿᶜᵗᵒʳ B) → (A →ᶠᵘⁿᶜᵗᵒʳ C)
  ∃.witness (_∘ᶠᵘⁿᶜᵗᵒʳ_ ([∃]-intro F)               ([∃]-intro G))               = Raw._∘ᶠᵘⁿᶜᵗᵒʳ_ F G
  ∃.proof   (_∘ᶠᵘⁿᶜᵗᵒʳ_ ([∃]-intro _ ⦃ F-functor ⦄) ([∃]-intro _ ⦃ G-functor ⦄)) = composition F-functor G-functor
