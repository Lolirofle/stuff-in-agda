import      Lvl
open import Type

module Structure.IndexedRelator.Properties
  {ℓᵢ : Lvl.Level}
  (Index : Type{ℓᵢ})
  {ℓₒ : Index → Lvl.Level}
  {ℓₘ : Index → Index → Lvl.Level}
  where

open import Structure.Setoid

private variable i i₁ i₂ i₃ i₄ : Index

module _
  (Obj : (i : Index) → Type{ℓₒ i})
  (_⟶_ : ∀{i₁ i₂} → Obj(i₁) → Obj(i₂) → Type{ℓₘ i₁ i₂})
  where

  module Names where
    FlippedTransitivity = ∀{i₁ i₂ i₃}{x : Obj(i₁)}{y : Obj(i₂)}{z : Obj(i₃)} → (y ⟶ z) → (x ⟶ y) → (x ⟶ z)
    Reflexivity = ∀{i}{x : Obj(i)} → (x ⟶ x)
