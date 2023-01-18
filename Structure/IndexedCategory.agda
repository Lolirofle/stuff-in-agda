import      Lvl
open import Type

module Structure.IndexedCategory
  {ℓᵢ : Lvl.Level}
  (Index : Type{ℓᵢ})
  {ℓₒ : Index → Lvl.Level}
  {ℓₘ ℓₑ : Index → Index → Lvl.Level}
  where

open import Structure.IndexedOperator.Properties(Index)
open import Structure.IndexedRelator.Properties(Index)
open import Structure.Operator
open import Structure.Setoid

private variable i i₁ i₂ i₃ i₄ : Index

module _
  (Obj : (i : Index) → Type{ℓₒ i})
  (_⟶_ : ∀{i₁ i₂} → Obj(i₁) → Obj(i₂) → Type{ℓₘ i₁ i₂})
  ⦃ morphism-equiv : ∀{i₁ i₂}{x : Obj(i₁)}{y : Obj(i₂)} → Equiv{ℓₑ i₁ i₂}(x ⟶ y) ⦄
  where

  private variable x y z : Obj(i)

  module _ (_∘_ : Names.FlippedTransitivity(Obj)(_⟶_)) (id : Names.Reflexivity(Obj)(_⟶_)) where
    -- Note: In theory, this could potentially be in a smaller universe level than Typeω if the image of the level functions would be finite (for example by having Index being be a finite type, or by having them not depend on the index).
    -- Note: A category could be seen as having Unit as the index.
    record Properties : Typeω where
      field
        ⦃ binaryOperator ⦄ : BinaryOperator(_∘_ {x = x}{y = y}{z = z})
        ⦃ associativity ⦄ : Associativity(Obj)(_⟶_)(_∘_)
        ⦃ identity ⦄ : Identity(Obj)(_⟶_)(_∘_)(id)

  record IndexedCategory : Typeω where
    constructor intro
    field
      _∘_ : Names.FlippedTransitivity(Obj)(_⟶_)
      id : Names.Reflexivity(Obj)(_⟶_)
      properties : Properties(_∘_)(id)

record IndexedCategoryObject : Typeω where
  constructor intro
  field
    Object : (i : Index) → Type{ℓₒ i}
    Morphism : ∀{i₁ i₂} → Object(i₁) → Object(i₂) → Type{ℓₘ i₁ i₂}
    ⦃ morphism-equiv ⦄ : ∀{i₁ i₂}{x : Object(i₁)}{y : Object(i₂)} → Equiv{ℓₑ i₁ i₂}(Morphism x y)
    indexedCategory : IndexedCategory Object Morphism
