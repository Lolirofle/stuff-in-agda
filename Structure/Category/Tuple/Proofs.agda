import      Lvl
open import Structure.Category

module Structure.Category.Tuple.Proofs
  {ℓₒ ℓₘ ℓₑ : Lvl.Level}
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} (let open CategoryObject(C)) (let open ArrowNotation)
  where

open import Structure.Categorical.Properties
open import Structure.Category.Tuple {C = C}
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

module _
  {_⨯_}
  ⦃ tuple : Tuple(_⨯_) ⦄
  where

  open Tuple(tuple)
  private open module MorphismEquiv{x}{y} = Equiv(morphism-equiv{x}{y}) using () public

  [<,>]-proj-inverse : ∀{x y} → (projₗ <,> projᵣ ≡ id{x ⨯ y})
  [<,>]-proj-inverse = symmetry(_≡_) (uniqueness-condition(Morphism.identityᵣ(_∘_)(id)) (Morphism.identityᵣ(_∘_)(id)))

  [<,>]-function : ∀{x y z}{f₁ f₂ : x ⟶ y}{g₁ g₂ : x ⟶ z} → (f₁ ≡ f₂) → (g₁ ≡ g₂) → (f₁ <,> g₁ ≡ f₂ <,> g₂)
  [<,>]-function pf pg = uniqueness-condition (projₗ-condition 🝖 pf) (projᵣ-condition 🝖 pg)

  [∘][<,>]-distributivityᵣ : ∀{x y z₁ z₂}{f : y ⟶ z₁}{g : y ⟶ z₂}{h : x ⟶ y} → (f <,> g) ∘ h ≡ ((f ∘ h) <,> (g ∘ h))
  [∘][<,>]-distributivityᵣ {x}{y}{z₁}{z₂}{f}{g}{h} = uniqueness-condition
    (
      projₗ ∘ ((f <,> g) ∘ h) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
      (projₗ ∘ (f <,> g)) ∘ h 🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(h) projₗ-condition ]
      f ∘ h                   🝖-end
    )
    (
      projᵣ ∘ ((f <,> g) ∘ h) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
      (projᵣ ∘ (f <,> g)) ∘ h 🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(h) projᵣ-condition ]
      g ∘ h                   🝖-end
    )
