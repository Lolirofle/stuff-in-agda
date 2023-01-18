import      Lvl
open import Structure.Category

module Structure.Category.Product.Tuple
  {ℓₒ ℓₘ ℓₑ : Lvl.Level}
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} (let open CategoryObject(C)) (let open ArrowNotation)
  where

-- TODO: This works, but maybe define the tuple product using _⨯_ instead of Π
import      Data.Tuple as Type
open import Data.Tuple.Category
open import Data.Boolean as Bool
open import Structure.Category.Product {C = C}
open import Structure.Setoid
open import Type

Tuple : (Object → Object → Object) → Type
Tuple(_⨯_) = Product(Bool) (\p → p(𝐹) ⨯ p(𝑇))
module Tuple{_⨯_} (T : Tuple(_⨯_)) where
  open Product(T) renaming (uniqueness-condition to u-condition)

  _<,>_  : ∀{x y z} → (x ⟶ y) → (x ⟶ z) → (x ⟶ (y ⨯ z))
  _<,>_ {x}{y}{z} f g = prod{x}{if_then z else y} (elim _ g f)

  projₗ : ∀{x y} → ((x ⨯ y) ⟶ x)
  projₗ{x}{y} = proj{if_then y else x} 𝐹

  projᵣ : ∀{x y} → ((x ⨯ y) ⟶ y)
  projᵣ{x}{y} = proj{if_then y else x} 𝑇

  projₗ-condition : ∀{x y z}{f : x ⟶ y}{g : x ⟶ z} → (projₗ ∘ (f <,> g) ≡ f)
  projₗ-condition = inverse-condition

  projᵣ-condition : ∀{x y z}{f : x ⟶ y}{g : x ⟶ z} → (projᵣ ∘ (f <,> g) ≡ g)
  projᵣ-condition = inverse-condition

  uniqueness-condition : ∀{x y z}{f : x ⟶ y}{g : x ⟶ z}{h : x ⟶ (y ⨯ z)} → (projₗ ∘ h ≡ f) → (projᵣ ∘ h ≡ g) → (h ≡ (f <,> g))
  uniqueness-condition l r = u-condition(\{ {𝐹} → l ; {𝑇} → r })

{-
import      Functional as Fn
open import Structure.Categorical.Properties

module _
  {_⨯_}{𝟏}
  ⦃ tuple : Tuple(_⨯_) ⦄
  ⦃ terminal : Object.Terminal(_⟶_)(𝟏) ⦄
  where

  import      Data.Tuple as Tuple
  open import Logic.Predicate
  open import Structure.Category.Functor
  open import Structure.Category.Monoidal
  open import Syntax.Transitivity
  private open module MorphismEquiv{x}{y} = Equiv(morphism-equiv{x}{y}) using () public

  monoidal : Monoidalᶜᵃᵗ(C) -- TODO: I don't have time for this now. Maybe for another time
  Monoidalᶜᵃᵗ.productFunctor monoidal = {!!}
  Monoidalᶜᵃᵗ.unitObject     monoidal = 𝟏
  MonoidalCategory.associator (Monoidalᶜᵃᵗ.monoidalCategory monoidal) = {!!}
  MonoidalCategory.unitorₗ    (Monoidalᶜᵃᵗ.monoidalCategory monoidal) = {!!}
  MonoidalCategory.unitorᵣ    (Monoidalᶜᵃᵗ.monoidalCategory monoidal) = {!!}
  MonoidalCategory.associativity-condition (Monoidalᶜᵃᵗ.monoidalCategory monoidal) = {!!}
  MonoidalCategory.unitality-condition     (Monoidalᶜᵃᵗ.monoidalCategory monoidal) = {!!}
-}

{- TODO: Here is Product which originally was in Structure.Category.Monoidal.Diagonal. It was defined in the context of an existing monoidal category and assumed that _⊗_ was used for the product instead. I tried to prove that <⊗> would be equivalent to <,> but it did not not seem to be provable from only these conditions. In Structure.Category.Product, the reverse was tried, to prove Monoidal from a <,> which should be possible.
record Product : Type{ℓₒ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    _<,>_  : ∀{x y z} → (x ⟶ y) → (x ⟶ z) → (x ⟶ (y ⊗ z))
    projₗ : ∀{x y} → ((x ⊗ y) ⟶ x)
    projᵣ : ∀{x y} → ((x ⊗ y) ⟶ y)
  field
    projₗ-condition : ∀{x y z}{f : x ⟶ y}{g : x ⟶ z} → (projₗ ∘ (f <,> g) ≡ f)
    projᵣ-condition : ∀{x y z}{f : x ⟶ y}{g : x ⟶ z} → (projᵣ ∘ (f <,> g) ≡ g)
    uniqueness-condition : ∀{x y z}{f : x ⟶ y}{g : x ⟶ z}{h : x ⟶ (y ⊗ z)} → (projₗ ∘ h ≡ f) → (projᵣ ∘ h ≡ g) → (h ≡ (f <,> g))

  open import Syntax.Transitivity
  private open module MorphismEquiv{x}{y} = Equiv(morphism-equiv{x}{y}) using () public

  test : ∀{x₁ x₂ y₁ y₂}{f : x₁ ⟶ y₁}{g : x₂ ⟶ y₂} → (projₗ ∘ (f <⊗> g) ≡ f ∘ projₗ)
  test = {!!}

  [<,>][<⊗>]-equality : ∀{x₁ x₂ y₁ y₂}{f : x₁ ⟶ y₁}{g : x₂ ⟶ y₂} → (f <⊗> g ≡ (f ∘ projₗ) <,> (g ∘ projᵣ))
  [<,>][<⊗>]-equality = uniqueness-condition {!!} {!!}
  -- [<,>][<⊗>]-equality' : ∀{x₁ x₂ y z}{f : (x₁ ⊗ x₂) ⟶ y}{g : (x₁ ⊗ x₂) ⟶ z} → ((f <,> g) ∘ {!!} ≡ (f <⊗> g))

  instance
    diagonal : Diagonal
    Singleton.IsUnit.unit       (Diagonal.terminal diagonal {x}) = projₗ ∘ υₗ⁻¹(x)
    Singleton.IsUnit.uniqueness (Diagonal.terminal diagonal {x}) {f} =
      f                          🝖[ _≡_ ]-[ projₗ-condition ]-sym
      projₗ ∘ (f <,> id)   🝖[ _≡_ ]-[ {!!} ]
      projₗ ∘ υₗ⁻¹(x)      🝖-end
    Diagonal.diag diagonal x = id{x} <,> id{x}
    Diagonal.identityₗ-condition diagonal = {!!}
    Diagonal.identityᵣ-condition diagonal = {!!}
-}
