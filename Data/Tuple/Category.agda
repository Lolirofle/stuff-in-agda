module Data.Tuple.Category where

import      Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Equivalence
import      Functional as Fn
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.Functor.Functors
open import Structure.Categorical.Functor.Properties
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
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

  tupleCategory : Category{Obj = Obj₁ ⨯ Obj₂} (Tuple.uncurry(_⨯_) Fn.∘₂ Tuple.map₂(Morphism₁)(Morphism₂))
  Category._∘_ tupleCategory = Tuple.map₂(_∘_)(_∘_)
  Category.id  tupleCategory = (id , id)
  BinaryOperator.congruence (Category.binaryOperator tupleCategory) (p₁l , p₁r) (p₂l , p₂r) = [∧]-intro (congruence₂(_∘_) p₁l p₂l) (congruence₂(_∘_) p₁r p₂r)
  Morphism.Associativity.proof (Category.associativity tupleCategory) = [∧]-intro (Morphism.associativity(_∘_)) (Morphism.associativity(_∘_))
  Morphism.Identityₗ.proof (_⨯_.left  (Category.identity tupleCategory)) = [∧]-intro (Morphism.identityₗ(_∘_)(id)) (Morphism.identityₗ(_∘_)(id))
  Morphism.Identityᵣ.proof (_⨯_.right (Category.identity tupleCategory)) = [∧]-intro (Morphism.identityᵣ(_∘_)(id)) (Morphism.identityᵣ(_∘_)(id))

_⨯ᶜᵃᵗ_ : CategoryObject{ℓₒ₁}{ℓₘ₁}{ℓₑ₁} → CategoryObject{ℓₒ₂}{ℓₘ₂}{ℓₑ₂} → CategoryObject
(intro C₁) ⨯ᶜᵃᵗ (intro C₂) = intro (tupleCategory C₁ C₂)

module Tupleᶜᵃᵗ where
  open CategoryObject ⦃ … ⦄
  open Functor ⦃ … ⦄ renaming (map to fmap)
  private open module CategoryObjectEquiv {ℓₒ ℓₘ ℓₑ} ⦃ C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ} ⦄ {x}{y} = Equivalence (Equiv-equivalence ⦃ CategoryObject.morphism-equiv(C){x}{y} ⦄) using ()

  open Structure.Category.Functor.Functors.Wrapped

  map : (C₁ₗ →ᶠᵘⁿᶜᵗᵒʳ C₁ᵣ) → (C₂ₗ →ᶠᵘⁿᶜᵗᵒʳ C₂ᵣ) → ((C₁ₗ ⨯ᶜᵃᵗ C₂ₗ) →ᶠᵘⁿᶜᵗᵒʳ (C₁ᵣ ⨯ᶜᵃᵗ C₂ᵣ))
  map {C₁ₗ = C₁ₗ} {C₁ᵣ = C₁ᵣ} {C₂ₗ = C₂ₗ} {C₂ᵣ = C₂ᵣ} ([∃]-intro F₁ ⦃ functor₁ ⦄) ([∃]-intro F₂ ⦃ functor₂ ⦄) = [∃]-intro _ ⦃ tupleMapFunctor ⦄ where
    instance _ = C₁ₗ ; instance _ = C₁ᵣ ; instance _ = C₂ₗ ; instance _ = C₂ᵣ
    instance _ = C₁ₗ ⨯ᶜᵃᵗ C₂ₗ ; instance _ = C₁ᵣ ⨯ᶜᵃᵗ C₂ᵣ
    tupleMapFunctor : Functor(tupleCategory (category ⦃ C₁ₗ ⦄) (category ⦃ C₂ₗ ⦄))(tupleCategory (category ⦃ C₁ᵣ ⦄) (category ⦃ C₂ᵣ ⦄)) (Tuple.map F₁ F₂)
    Functor.map tupleMapFunctor = Tuple.map fmap fmap
    Functor.op-preserving tupleMapFunctor = intro([∧]-intro (preserving₂ _ _ _ _ _ ⦃ op-preserving ⦄) (preserving₂ _ _ _ _ _ ⦃ op-preserving ⦄))
    Functor.id-preserving tupleMapFunctor = intro([∧]-intro (preserving₀ _ _ _ _ _ ⦃ id-preserving ⦄) (preserving₀ _ _ _ _ _ ⦃ id-preserving ⦄))

  mapLeft : (C₁ₗ →ᶠᵘⁿᶜᵗᵒʳ C₁ᵣ) → ((C₁ₗ ⨯ᶜᵃᵗ C₂) →ᶠᵘⁿᶜᵗᵒʳ (C₁ᵣ ⨯ᶜᵃᵗ C₂))
  mapLeft F = map F idᶠᵘⁿᶜᵗᵒʳ

  mapRight : (C₂ₗ →ᶠᵘⁿᶜᵗᵒʳ C₂ᵣ) → ((C₁ ⨯ᶜᵃᵗ C₂ₗ) →ᶠᵘⁿᶜᵗᵒʳ (C₁ ⨯ᶜᵃᵗ C₂ᵣ))
  mapRight F = map idᶠᵘⁿᶜᵗᵒʳ F

  left : ((Cₗ ⨯ᶜᵃᵗ Cᵣ) →ᶠᵘⁿᶜᵗᵒʳ Cₗ)
  ∃.witness left = Tuple.left
  Functor.map (∃.proof left) = Tuple.left
  Functor.op-preserving (∃.proof (left {Cₗ = Cₗ} {Cᵣ = Cᵣ})) =
    intro \{ {fₗ , fᵣ} {gₗ , gᵣ} →
      Tuple.left((fₗ , fᵣ) ∘ (gₗ , gᵣ))         🝖[ _≡_ ]-[]
      Tuple.left((fₗ ∘ gₗ) , (fᵣ ∘ gᵣ))         🝖[ _≡_ ]-[]
      fₗ ∘ gₗ                                   🝖[ _≡_ ]-[]
      Tuple.left(fₗ , fᵣ) ∘ Tuple.left(gₗ , gᵣ) 🝖-end
    } where instance _ = Cₗ ; instance _ = Cᵣ ; instance _ = Cₗ ⨯ᶜᵃᵗ Cᵣ
  Functor.id-preserving (∃.proof (left {Cₗ = Cₗ} {Cᵣ = Cᵣ})) {x , y} =
    intro Fn.$
      Tuple.left (id ⦃ Cₗ ⨯ᶜᵃᵗ Cᵣ ⦄ {x , y})      🝖[ _≡_ ]-[]
      Tuple.left (id ⦃ Cₗ ⦄ {x} , id ⦃ Cᵣ ⦄ {y})  🝖[ _≡_ ]-[]
      id ⦃ Cₗ ⦄ {x}                               🝖-end
    where instance _ = Cₗ ; instance _ = Cᵣ ; instance _ = Cₗ ⨯ᶜᵃᵗ Cᵣ

  right : ((Cₗ ⨯ᶜᵃᵗ Cᵣ) →ᶠᵘⁿᶜᵗᵒʳ Cᵣ)
  ∃.witness right = Tuple.right
  Functor.map (∃.proof right) = Tuple.right
  Functor.op-preserving (∃.proof (right {Cₗ = Cₗ} {Cᵣ = Cᵣ})) =
    intro \{ {fₗ , fᵣ} {gₗ , gᵣ} →
      Tuple.right ((fₗ , fᵣ) ∘ (gₗ , gᵣ))        🝖[ _≡_ ]-[]
      Tuple.right ((fₗ ∘ gₗ) , (fᵣ ∘ gᵣ))        🝖[ _≡_ ]-[]
      fᵣ ∘ gᵣ                                    🝖[ _≡_ ]-[]
      Tuple.right(fₗ , fᵣ) ∘ Tuple.right(gₗ , gᵣ) 🝖-end
    } where instance _ = Cₗ ; instance _ = Cᵣ ; instance _ = Cₗ ⨯ᶜᵃᵗ Cᵣ
  Functor.id-preserving (∃.proof (right {Cₗ = Cₗ} {Cᵣ = Cᵣ})) {x , y} =
    intro Fn.$
      Tuple.right (id ⦃ Cₗ ⨯ᶜᵃᵗ Cᵣ ⦄ {x , y})      🝖[ _≡_ ]-[]
      Tuple.right (id ⦃ Cₗ ⦄ {x} , id ⦃ Cᵣ ⦄ {y})  🝖[ _≡_ ]-[]
      id ⦃ Cᵣ ⦄ {y}                                🝖-end
    where instance _ = Cₗ ; instance _ = Cᵣ ; instance _ = Cₗ ⨯ᶜᵃᵗ Cᵣ

  diag : (C →ᶠᵘⁿᶜᵗᵒʳ (C ⨯ᶜᵃᵗ C))
  ∃.witness diag = Tuple.diag
  Functor.map (∃.proof diag) = Tuple.diag
  Functor.op-preserving (∃.proof (diag {C = C})) =
    intro \{f}{g} →
      Tuple.diag(f ∘ g)               🝖[ _≡_ ]-[]
      Tuple.diag(f) ∘ Tuple.diag(g) 🝖-end
    where instance _ = C ; instance _ = C ⨯ᶜᵃᵗ C
  (Functor.id-preserving (∃.proof (diag {C = C})) {x}) =
    intro Fn.$
      Tuple.diag(id{x = x})  🝖[ _≡_ ]-[]
      id{x = (x , x)}          🝖-end
    where instance _ = C ; instance _ = C ⨯ᶜᵃᵗ C

  constₗ : CategoryObject.Object(Cₗ) → (Cᵣ →ᶠᵘⁿᶜᵗᵒʳ (Cₗ ⨯ᶜᵃᵗ Cᵣ))
  constₗ c = mapLeft (constᶠᵘⁿᶜᵗᵒʳ c) ∘ᶠᵘⁿᶜᵗᵒʳ diag

  constᵣ : CategoryObject.Object(Cᵣ) → (Cₗ →ᶠᵘⁿᶜᵗᵒʳ (Cₗ ⨯ᶜᵃᵗ Cᵣ))
  constᵣ c = mapRight (constᶠᵘⁿᶜᵗᵒʳ c) ∘ᶠᵘⁿᶜᵗᵒʳ diag

  associateLeft : (C₁ ⨯ᶜᵃᵗ (C₂ ⨯ᶜᵃᵗ C₃)) →ᶠᵘⁿᶜᵗᵒʳ ((C₁ ⨯ᶜᵃᵗ C₂) ⨯ᶜᵃᵗ C₃)
  ∃.witness associateLeft = Tuple.associateLeft
  Functor.map (∃.proof associateLeft) = Tuple.associateLeft
  Functor.op-preserving (∃.proof (associateLeft {C₁ = C₁}{C₂ = C₂}{C₃ = C₃})) =
    intro \{f}{g} →
      Tuple.associateLeft(f ∘ g)                    🝖[ _≡_ ]-[]
      Tuple.associateLeft f ∘ Tuple.associateLeft g 🝖-end
    where
      instance _ = C₁ ; instance _ = C₂ ; instance _ = C₃
      instance _ = C₁ ⨯ᶜᵃᵗ C₂ ; instance _ = C₂ ⨯ᶜᵃᵗ C₃
      instance _ = C₁ ⨯ᶜᵃᵗ (C₂ ⨯ᶜᵃᵗ C₃) ; instance _ = (C₁ ⨯ᶜᵃᵗ C₂) ⨯ᶜᵃᵗ C₃
  Functor.id-preserving (∃.proof (associateLeft {C₁ = C₁}{C₂ = C₂}{C₃ = C₃})) =
    intro Fn.$
      Tuple.associateLeft(id) 🝖[ _≡_ ]-[]
      id                      🝖-end
    where
      instance _ = C₁ ; instance _ = C₂ ; instance _ = C₃
      instance _ = C₁ ⨯ᶜᵃᵗ C₂ ; instance _ = C₂ ⨯ᶜᵃᵗ C₃
      instance _ = C₁ ⨯ᶜᵃᵗ (C₂ ⨯ᶜᵃᵗ C₃) ; instance _ = (C₁ ⨯ᶜᵃᵗ C₂) ⨯ᶜᵃᵗ C₃

  associateRight : ((C₁ ⨯ᶜᵃᵗ C₂) ⨯ᶜᵃᵗ C₃) →ᶠᵘⁿᶜᵗᵒʳ (C₁ ⨯ᶜᵃᵗ (C₂ ⨯ᶜᵃᵗ C₃))
  ∃.witness associateRight = Tuple.associateRight
  Functor.map (∃.proof associateRight) = Tuple.associateRight
  Functor.op-preserving (∃.proof (associateRight {C₁ = C₁}{C₂ = C₂}{C₃ = C₃})) =
    intro \{f}{g} →
      Tuple.associateRight(f ∘ g)                    🝖[ _≡_ ]-[]
      Tuple.associateRight f ∘ Tuple.associateRight g 🝖-end
    where
      instance _ = C₁ ; instance _ = C₂ ; instance _ = C₃
      instance _ = C₁ ⨯ᶜᵃᵗ C₂ ; instance _ = C₂ ⨯ᶜᵃᵗ C₃
      instance _ = C₁ ⨯ᶜᵃᵗ (C₂ ⨯ᶜᵃᵗ C₃) ; instance _ = (C₁ ⨯ᶜᵃᵗ C₂) ⨯ᶜᵃᵗ C₃
  Functor.id-preserving (∃.proof (associateRight {C₁ = C₁}{C₂ = C₂}{C₃ = C₃})) =
    intro Fn.$
      Tuple.associateRight(id) 🝖[ _≡_ ]-[]
      id                       🝖-end
    where
      instance _ = C₁ ; instance _ = C₂ ; instance _ = C₃
      instance _ = C₁ ⨯ᶜᵃᵗ C₂ ; instance _ = C₂ ⨯ᶜᵃᵗ C₃
      instance _ = C₁ ⨯ᶜᵃᵗ (C₂ ⨯ᶜᵃᵗ C₃) ; instance _ = (C₁ ⨯ᶜᵃᵗ C₂) ⨯ᶜᵃᵗ C₃

  _on₂_ : let _ = C₁ in ((C₂ ⨯ᶜᵃᵗ C₂) →ᶠᵘⁿᶜᵗᵒʳ C₃) → (C₁ →ᶠᵘⁿᶜᵗᵒʳ C₂) → ((C₁ ⨯ᶜᵃᵗ C₁) →ᶠᵘⁿᶜᵗᵒʳ C₃)
  F on₂ G = F ∘ᶠᵘⁿᶜᵗᵒʳ (map G G)
