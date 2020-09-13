module Data.Tuple.Category where

import      Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Equiv
import      Functional as Fn
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.Functor.Functors
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid.WithLvl
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₒ ℓₘ ℓₑ ℓₒ₁ ℓₘ₁ ℓₑ₁ ℓₒ₂ ℓₘ₂ ℓₑ₂ : Lvl.Level
private variable Obj Obj₁ Obj₂ Obj₁ₗ Obj₁ᵣ Obj₂ₗ Obj₂ᵣ : Type{ℓ}
private variable Morphism Morphism₁ Morphism₂ Morphism₁ₗ Morphism₂ₗ Morphism₁ᵣ Morphism₂ᵣ : Obj → Obj → Type{ℓ}
private variable ⦃ morphism-equiv morphism-equiv₁ morphism-equiv₂ morphism-equiv₁ₗ morphism-equiv₂ₗ morphism-equiv₁ᵣ morphism-equiv₂ᵣ ⦄ : ∀{x y : Obj} → Equiv{ℓₑ}(Morphism x y)
private variable F F₁ F₂ : Obj₁ → Obj₂
private variable C Cₗ Cᵣ C₁ₗ C₁ᵣ C₂ₗ C₂ᵣ C₁ C₂ C₃ : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}

module _
  (cat₁ : Category{Obj = Obj₁} (Morphism₁) ⦃ \{x y} → morphism-equiv₁{x}{y} ⦄)
  (cat₂ : Category{Obj = Obj₂} (Morphism₂) ⦃ \{x y} → morphism-equiv₂{x}{y} ⦄)
  where

  open Category ⦃ … ⦄

  private instance _ = cat₁
  private instance _ = cat₂

  productCategory : Category{Obj = Obj₁ ⨯ Obj₂} (\{(x₁ , x₂) (y₁ , y₂) → (Morphism₁ x₁ y₁) ⨯ (Morphism₂ x₂ y₂)})
  Category._∘_ productCategory (f₁ , f₂) (g₁ , g₂) = ((f₁ ∘ g₁) , (f₂ ∘ g₂))
  Category.id  productCategory                     = (id , id)
  _⨯_.left  (BinaryOperator.congruence (Category.binaryOperator productCategory) (p₁l , p₁r) (p₂l , p₂r)) = congruence₂(_∘_) p₁l p₂l
  _⨯_.right (BinaryOperator.congruence (Category.binaryOperator productCategory) (p₁l , p₁r) (p₂l , p₂r)) = congruence₂(_∘_) p₁r p₂r
  _⨯_.left  (Morphism.Associativity.proof (Category.associativity productCategory)) = Morphism.associativity(_∘_)
  _⨯_.right (Morphism.Associativity.proof (Category.associativity productCategory)) = Morphism.associativity(_∘_)
  _⨯_.left  (Morphism.Identityₗ.proof (_⨯_.left  (Category.identity productCategory))) = Morphism.identityₗ(_∘_)(id)
  _⨯_.right (Morphism.Identityₗ.proof (_⨯_.left  (Category.identity productCategory))) = Morphism.identityₗ(_∘_)(id)
  _⨯_.left  (Morphism.Identityᵣ.proof (_⨯_.right (Category.identity productCategory))) = Morphism.identityᵣ(_∘_)(id)
  _⨯_.right (Morphism.Identityᵣ.proof (_⨯_.right (Category.identity productCategory))) = Morphism.identityᵣ(_∘_)(id)

_⨯ᶜᵃᵗ_ : CategoryObject{ℓₒ₁}{ℓₘ₁}{ℓₑ₁} → CategoryObject{ℓₒ₂}{ℓₘ₂}{ℓₑ₂} → CategoryObject
(intro C₁) ⨯ᶜᵃᵗ (intro C₂) = intro (productCategory C₁ C₂)

module Tupleᶜᵃᵗ where
  open CategoryObject ⦃ … ⦄
  open Functor ⦃ … ⦄ renaming (map to fmap)
  private open module CategoryObjectEquiv {ℓₒ ℓₘ ℓₑ} ⦃ C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ} ⦄ {x}{y} = Equivalence (Equiv-equivalence ⦃ CategoryObject.morphism-equiv(C){x}{y} ⦄) using ()
  private open module CategoryObjectCategory {ℓₒ ℓₘ ℓₑ} ⦃ C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ} ⦄ = Category(category ⦃ C ⦄)

  open Structure.Category.Functor.Functors.Wrapped

  map : (C₁ₗ →ᶠᵘⁿᶜᵗᵒʳ C₁ᵣ) → (C₂ₗ →ᶠᵘⁿᶜᵗᵒʳ C₂ᵣ) → ((C₁ₗ ⨯ᶜᵃᵗ C₂ₗ) →ᶠᵘⁿᶜᵗᵒʳ (C₁ᵣ ⨯ᶜᵃᵗ C₂ᵣ))
  map {C₁ₗ = C₁ₗ} {C₁ᵣ = C₁ᵣ} {C₂ₗ = C₂ₗ} {C₂ᵣ = C₂ᵣ} ([∃]-intro F₁ ⦃ functor₁ ⦄) ([∃]-intro F₂ ⦃ functor₂ ⦄) = [∃]-intro _ ⦃ productMapFunctor ⦄ where
    instance _ = C₁ₗ ; instance _ = C₁ᵣ ; instance _ = C₂ₗ ; instance _ = C₂ᵣ
    instance _ = C₁ₗ ⨯ᶜᵃᵗ C₂ₗ ; instance _ = C₁ᵣ ⨯ᶜᵃᵗ C₂ᵣ
    productMapFunctor : Functor(productCategory (category ⦃ C₁ₗ ⦄) (category ⦃ C₂ₗ ⦄))(productCategory (category ⦃ C₁ᵣ ⦄) (category ⦃ C₂ᵣ ⦄)) (Tuple.map F₁ F₂)
    Functor.map productMapFunctor = Tuple.map fmap fmap
    Tuple.left  (Functor.op-preserving productMapFunctor) = op-preserving
    Tuple.right (Functor.op-preserving productMapFunctor) = op-preserving
    Tuple.left  (Functor.id-preserving productMapFunctor) = id-preserving
    Tuple.right (Functor.id-preserving productMapFunctor) = id-preserving

  mapLeft : (C₁ₗ →ᶠᵘⁿᶜᵗᵒʳ C₁ᵣ) → ((C₁ₗ ⨯ᶜᵃᵗ C₂) →ᶠᵘⁿᶜᵗᵒʳ (C₁ᵣ ⨯ᶜᵃᵗ C₂))
  mapLeft F = map F idᶠᵘⁿᶜᵗᵒʳ

  mapRight : (C₂ₗ →ᶠᵘⁿᶜᵗᵒʳ C₂ᵣ) → ((C₁ ⨯ᶜᵃᵗ C₂ₗ) →ᶠᵘⁿᶜᵗᵒʳ (C₁ ⨯ᶜᵃᵗ C₂ᵣ))
  mapRight F = map idᶠᵘⁿᶜᵗᵒʳ F

  left : ((Cₗ ⨯ᶜᵃᵗ Cᵣ) →ᶠᵘⁿᶜᵗᵒʳ Cₗ)
  ∃.witness left = Tuple.left
  Functor.map (∃.proof left) = Tuple.left
  Functor.op-preserving (∃.proof (left {Cₗ = Cₗ} {Cᵣ = Cᵣ})) {f = (fₗ , fᵣ)} {g = (gₗ , gᵣ)} =
    Tuple.left ((fₗ , fᵣ) ∘ (gₗ , gᵣ))        🝖[ _≡_ ]-[]
    Tuple.left ((fₗ ∘ gₗ) , (fᵣ ∘ gᵣ))        🝖[ _≡_ ]-[]
    fₗ ∘ gₗ                                   🝖[ _≡_ ]-[]
    Tuple.left(fₗ , fᵣ) ∘ Tuple.left(gₗ , gᵣ) 🝖-end
    where instance _ = Cₗ ; instance _ = Cᵣ ; instance _ = Cₗ ⨯ᶜᵃᵗ Cᵣ
  Functor.id-preserving (∃.proof (left {Cₗ = Cₗ} {Cᵣ = Cᵣ})) {x , y} =
    Tuple.left (id ⦃ Cₗ ⨯ᶜᵃᵗ Cᵣ ⦄ {x , y})      🝖[ _≡_ ]-[]
    Tuple.left (id ⦃ Cₗ ⦄ {x} , id ⦃ Cᵣ ⦄ {y})  🝖[ _≡_ ]-[]
    id ⦃ Cₗ ⦄ {x}                               🝖-end
    where instance _ = Cₗ ; instance _ = Cᵣ ; instance _ = Cₗ ⨯ᶜᵃᵗ Cᵣ

  right : ((Cₗ ⨯ᶜᵃᵗ Cᵣ) →ᶠᵘⁿᶜᵗᵒʳ Cᵣ)
  ∃.witness right = Tuple.right
  Functor.map (∃.proof right) = Tuple.right
  Functor.op-preserving (∃.proof (right {Cₗ = Cₗ} {Cᵣ = Cᵣ})) {f = (fₗ , fᵣ)} {g = (gₗ , gᵣ)} =
    Tuple.right ((fₗ , fᵣ) ∘ (gₗ , gᵣ))        🝖[ _≡_ ]-[]
    Tuple.right ((fₗ ∘ gₗ) , (fᵣ ∘ gᵣ))        🝖[ _≡_ ]-[]
    fᵣ ∘ gᵣ                                    🝖[ _≡_ ]-[]
    Tuple.right(fₗ , fᵣ) ∘ Tuple.right(gₗ , gᵣ) 🝖-end
    where instance _ = Cₗ ; instance _ = Cᵣ ; instance _ = Cₗ ⨯ᶜᵃᵗ Cᵣ
  Functor.id-preserving (∃.proof (right {Cₗ = Cₗ} {Cᵣ = Cᵣ})) {x , y} =
    Tuple.right (id ⦃ Cₗ ⨯ᶜᵃᵗ Cᵣ ⦄ {x , y})      🝖[ _≡_ ]-[]
    Tuple.right (id ⦃ Cₗ ⦄ {x} , id ⦃ Cᵣ ⦄ {y})  🝖[ _≡_ ]-[]
    id ⦃ Cᵣ ⦄ {y}                                🝖-end
    where instance _ = Cₗ ; instance _ = Cᵣ ; instance _ = Cₗ ⨯ᶜᵃᵗ Cᵣ

  repeat : (C →ᶠᵘⁿᶜᵗᵒʳ (C ⨯ᶜᵃᵗ C))
  ∃.witness repeat = Tuple.repeat
  Functor.map (∃.proof repeat) = Tuple.repeat
  Functor.op-preserving (∃.proof (repeat {C = C})) {f = f} {g = g} =
    Tuple.repeat(f ∘ g)               🝖[ _≡_ ]-[]
    Tuple.repeat(f) ∘ Tuple.repeat(g) 🝖-end
    where instance _ = C ; instance _ = C ⨯ᶜᵃᵗ C
  (Functor.id-preserving (∃.proof (repeat {C = C})) {x}) =
    Tuple.repeat(id{x = x})  🝖[ _≡_ ]-[]
    id{x = (x , x)}          🝖-end
    where instance _ = C ; instance _ = C ⨯ᶜᵃᵗ C

  constₗ : CategoryObject.Object(Cₗ) → (Cᵣ →ᶠᵘⁿᶜᵗᵒʳ (Cₗ ⨯ᶜᵃᵗ Cᵣ))
  constₗ c = mapLeft (constᶠᵘⁿᶜᵗᵒʳ c) ∘ᶠᵘⁿᶜᵗᵒʳ repeat

  constᵣ : CategoryObject.Object(Cᵣ) → (Cₗ →ᶠᵘⁿᶜᵗᵒʳ (Cₗ ⨯ᶜᵃᵗ Cᵣ))
  constᵣ c = mapRight (constᶠᵘⁿᶜᵗᵒʳ c) ∘ᶠᵘⁿᶜᵗᵒʳ repeat

  associateLeft : (C₁ ⨯ᶜᵃᵗ (C₂ ⨯ᶜᵃᵗ C₃)) →ᶠᵘⁿᶜᵗᵒʳ ((C₁ ⨯ᶜᵃᵗ C₂) ⨯ᶜᵃᵗ C₃)
  ∃.witness associateLeft = Tuple.associateLeft
  Functor.map (∃.proof associateLeft) = Tuple.associateLeft
  Functor.op-preserving (∃.proof (associateLeft {C₁ = C₁}{C₂ = C₂}{C₃ = C₃})) {f = f}{g = g} =
    Tuple.associateLeft(f ∘ g)                    🝖[ _≡_ ]-[]
    Tuple.associateLeft f ∘ Tuple.associateLeft g 🝖-end
    where
      instance _ = C₁ ; instance _ = C₂ ; instance _ = C₃
      instance _ = C₁ ⨯ᶜᵃᵗ C₂ ; instance _ = C₂ ⨯ᶜᵃᵗ C₃
      instance _ = C₁ ⨯ᶜᵃᵗ (C₂ ⨯ᶜᵃᵗ C₃) ; instance _ = (C₁ ⨯ᶜᵃᵗ C₂) ⨯ᶜᵃᵗ C₃
  Functor.id-preserving (∃.proof (associateLeft {C₁ = C₁}{C₂ = C₂}{C₃ = C₃})) =
    Tuple.associateLeft(id) 🝖[ _≡_ ]-[]
    id                      🝖-end
    where
      instance _ = C₁ ; instance _ = C₂ ; instance _ = C₃
      instance _ = C₁ ⨯ᶜᵃᵗ C₂ ; instance _ = C₂ ⨯ᶜᵃᵗ C₃
      instance _ = C₁ ⨯ᶜᵃᵗ (C₂ ⨯ᶜᵃᵗ C₃) ; instance _ = (C₁ ⨯ᶜᵃᵗ C₂) ⨯ᶜᵃᵗ C₃

  associateRight : ((C₁ ⨯ᶜᵃᵗ C₂) ⨯ᶜᵃᵗ C₃) →ᶠᵘⁿᶜᵗᵒʳ (C₁ ⨯ᶜᵃᵗ (C₂ ⨯ᶜᵃᵗ C₃))
  ∃.witness associateRight = Tuple.associateRight
  Functor.map (∃.proof associateRight) = Tuple.associateRight
  Functor.op-preserving (∃.proof (associateRight {C₁ = C₁}{C₂ = C₂}{C₃ = C₃})) {f = f}{g = g} =
    Tuple.associateRight(f ∘ g)                    🝖[ _≡_ ]-[]
    Tuple.associateRight f ∘ Tuple.associateRight g 🝖-end
    where
      instance _ = C₁ ; instance _ = C₂ ; instance _ = C₃
      instance _ = C₁ ⨯ᶜᵃᵗ C₂ ; instance _ = C₂ ⨯ᶜᵃᵗ C₃
      instance _ = C₁ ⨯ᶜᵃᵗ (C₂ ⨯ᶜᵃᵗ C₃) ; instance _ = (C₁ ⨯ᶜᵃᵗ C₂) ⨯ᶜᵃᵗ C₃
  Functor.id-preserving (∃.proof (associateRight {C₁ = C₁}{C₂ = C₂}{C₃ = C₃})) =
    Tuple.associateRight(id) 🝖[ _≡_ ]-[]
    id                       🝖-end
    where
      instance _ = C₁ ; instance _ = C₂ ; instance _ = C₃
      instance _ = C₁ ⨯ᶜᵃᵗ C₂ ; instance _ = C₂ ⨯ᶜᵃᵗ C₃
      instance _ = C₁ ⨯ᶜᵃᵗ (C₂ ⨯ᶜᵃᵗ C₃) ; instance _ = (C₁ ⨯ᶜᵃᵗ C₂) ⨯ᶜᵃᵗ C₃
