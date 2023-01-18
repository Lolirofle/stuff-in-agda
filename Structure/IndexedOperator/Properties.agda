import      Lvl
open import Type

module Structure.IndexedOperator.Properties
  {ℓᵢ : Lvl.Level}
  (Index : Type{ℓᵢ})
  {ℓₒ : Index → Lvl.Level}
  {ℓₘ ℓₑ : Index → Index → Lvl.Level}
  where

open import Structure.IndexedRelator.Properties Index
open import Structure.Setoid

private variable i i₁ i₂ i₃ i₄ : Index

module _
  (Obj : (i : Index) → Type{ℓₒ i})
  (_⟶_ : ∀{i₁ i₂} → Obj(i₁) → Obj(i₂) → Type{ℓₘ i₁ i₂})
  ⦃ morphism-equiv : ∀{i₁ i₂}{x : Obj(i₁)}{y : Obj(i₂)} → Equiv{ℓₑ i₁ i₂}(x ⟶ y) ⦄
  where

  module _ (_∘_ : Names.FlippedTransitivity(Obj)(_⟶_)) where
    record Associativity : Typeω where
      constructor intro
      field proof : ∀{x : Obj(i₁)}{y : Obj(i₂)}{z : Obj(i₃)}{w : Obj(i₄)}{f : y ⟶ x}{g : z ⟶ y}{h : w ⟶ z} → ((f ∘ g) ∘ h ≡ f ∘ (g ∘ h))

  module _ (_∘_ : Names.FlippedTransitivity(Obj)(_⟶_)) (id : Names.Reflexivity(Obj)(_⟶_)) where
    record Identityₗ : Typeω where
      constructor intro
      field proof : ∀{x : Obj(i₁)}{y : Obj(i₂)}{f : x ⟶ y} → (id ∘ f ≡ f)

    record Identityᵣ : Typeω where
      constructor intro
      field proof : ∀{x : Obj(i₁)}{y : Obj(i₂)}{f : x ⟶ y} → (f ∘ id ≡ f)

    open import Dataω.Tuple
    Identity = Identityₗ ⨯ Identityᵣ
