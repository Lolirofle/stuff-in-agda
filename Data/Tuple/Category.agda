module Data.Tuple.Category where

open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Equiv
open import Logic.Propositional
open import Structure.Setoid
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.Properties
open import Structure.Operator
open import Type

open Category ⦃ … ⦄

module Raw where
  module _
    {ℓₒ}
    (Obj₁ : Type{ℓₒ})
    (Obj₂ : Type{ℓₒ})
    where

    productObj : Type{ℓₒ}
    productObj = Obj₁ ⨯ Obj₂

  module _
    {ℓₒ ℓₘ}
    {Obj₁ : Type{ℓₒ}}
    {Obj₂ : Type{ℓₒ}}
    (Morphism₁ : Obj₁ → Obj₁ → Type{ℓₘ})
    (Morphism₂ : Obj₂ → Obj₂ → Type{ℓₘ})
    where

    productMorphism : productObj(Obj₁)(Obj₂) → productObj(Obj₁)(Obj₂) → Type{ℓₘ}
    productMorphism(x₁ , x₂) (y₁ , y₂) = (Morphism₁ x₁ y₁) ⨯ (Morphism₂ x₂ y₂)

  module _
    {ℓₒ}
    {Obj₁ₗ Obj₁ᵣ Obj₂ₗ Obj₂ᵣ : Type{ℓₒ}}
    where

    _⨯ᶠᵘⁿᶜᵗᵒʳ_ : (Obj₁ₗ → Obj₂ₗ) → (Obj₁ᵣ → Obj₂ᵣ) → (productObj(Obj₁ₗ)(Obj₁ᵣ) → productObj(Obj₂ₗ)(Obj₂ᵣ))
    (f ⨯ᶠᵘⁿᶜᵗᵒʳ g) (x₁ , x₂) = (f(x₁) , g(x₂))

module _
  {ℓₒ ℓₘ}
  {Obj₁ : Type{ℓₒ}}
  {Obj₂ : Type{ℓₒ}}
  {Morphism₁ : Obj₁ → Obj₁ → Type{ℓₘ}}
  {Morphism₂ : Obj₂ → Obj₂ → Type{ℓₘ}}
  ⦃ _ : ∀{x y} → Equiv(Morphism₁ x y) ⦄
  ⦃ _ : ∀{x y} → Equiv(Morphism₂ x y) ⦄
  (cat₁ : Category(Morphism₁))
  (cat₂ : Category(Morphism₂))
  where

  private instance _ = cat₁
  private instance _ = cat₂

  productCategory : Category(Raw.productMorphism(Morphism₁)(Morphism₂))
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

  _⨯ᶜᵃᵗ_ = productCategory

module _
  {ℓₒ ℓₘ}
  {Obj₁ₗ Obj₁ᵣ Obj₂ₗ Obj₂ᵣ : Type{ℓₒ}}
  {Morphism₁ₗ : Obj₁ₗ → Obj₁ₗ → Type{ℓₘ}}
  {Morphism₁ᵣ : Obj₁ᵣ → Obj₁ᵣ → Type{ℓₘ}}
  {Morphism₂ₗ : Obj₂ₗ → Obj₂ₗ → Type{ℓₘ}}
  {Morphism₂ᵣ : Obj₂ᵣ → Obj₂ᵣ → Type{ℓₘ}}
  ⦃ _ : ∀{x y} → Equiv(Morphism₁ₗ x y) ⦄
  ⦃ _ : ∀{x y} → Equiv(Morphism₁ᵣ x y) ⦄
  ⦃ _ : ∀{x y} → Equiv(Morphism₂ₗ x y) ⦄
  ⦃ _ : ∀{x y} → Equiv(Morphism₂ᵣ x y) ⦄
  {cat₁ₗ : Category(Morphism₁ₗ)}
  {cat₁ᵣ : Category(Morphism₁ᵣ)}
  {cat₂ₗ : Category(Morphism₂ₗ)}
  {cat₂ᵣ : Category(Morphism₂ᵣ)}
  {F₁ : Obj₁ₗ → Obj₂ₗ}
  {F₂ : Obj₁ᵣ → Obj₂ᵣ}
  (functorₗ : Functor(cat₁ₗ)(cat₂ₗ) (F₁))
  (functorᵣ : Functor(cat₁ᵣ)(cat₂ᵣ) (F₂))
  where

  private instance _ = functorₗ
  private instance _ = functorᵣ

  open Functor ⦃ … ⦄

  productFunctor : Functor(productCategory cat₁ₗ cat₁ᵣ)(productCategory cat₂ₗ cat₂ᵣ) (F₁ Raw.⨯ᶠᵘⁿᶜᵗᵒʳ F₂)
  Functor.map productFunctor (x₁ , x₂) = (map x₁ , map x₂)
  _⨯_.left  (Function.congruence (Functor.map-function productFunctor) (x₁ , x₂)) = congruence₁(map) x₁
  _⨯_.right (Function.congruence (Functor.map-function productFunctor) (x₁ , x₂)) = congruence₁(map) x₂
  _⨯_.left  (Functor.op-preserving productFunctor) = op-preserving
  _⨯_.right (Functor.op-preserving productFunctor) = op-preserving
  _⨯_.left  (Functor.id-preserving productFunctor) = id-preserving
  _⨯_.right (Functor.id-preserving productFunctor) = id-preserving
