module Signature.IndexedCategory where

import      Lvl
open import Structure.Setoid
open import Type

record IndexedCategory : Typeω where
  constructor indexedCategory
  field
    {ℓᵢ} : Lvl.Level
    Index : Type{ℓᵢ}
    {ℓₒ} : Index → Lvl.Level
    Obj : (i : Index) → Type{ℓₒ(i)}
    {ℓₘ} : Index → Index → Lvl.Level
    _⟶_ : ∀{i₁ i₂} → Obj(i₁) → Obj(i₂) → Type{ℓₘ i₁ i₂}
  MorphismEquiv = \(ℓₑₘ : Index → Index → Lvl.Level) → ∀{i₁ i₂}{x : Obj(i₁)}{y : Obj(i₂)} → Equiv{ℓₑₘ i₁ i₂}(x ⟶ y)
