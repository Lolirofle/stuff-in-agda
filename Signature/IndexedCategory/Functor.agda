module Signature.IndexedCategory.Functor where

import      Function as Fn
import      Lvl
open import Signature.IndexedCategory
open import Typeω.Dependent.Sigma
open import Type

-- The functor of two indexed category signatures.
-- Note: Not to be confused by the signature of the functor of two indexed categories.
record Functor(C₁ : IndexedCategory) (C₂ : IndexedCategory) : Typeω where
  constructor functor
  open IndexedCategory(C₁) using () renaming (Index to Index₁ ; Obj to Obj₁ ; _⟶_ to _⟶₁_) public
  open IndexedCategory(C₂) using () renaming (Index to Index₂ ; Obj to Obj₂ ; _⟶_ to _⟶₂_) public
  field
    index : Index₁ → Index₂
    obj   : ∀{i} → Obj₁(i) → Obj₂(index(i))
  Map = ∀{i₁ i₂}{A : Obj₁(i₁)}{B : Obj₁(i₂)} → (A ⟶₁ B) → (obj(A) ⟶₂ obj(B))

_→ᶠᵘⁿᶜᵗᵒʳ_ : IndexedCategory → IndexedCategory → Typeω
C₁ →ᶠᵘⁿᶜᵗᵒʳ C₂ = Σ(Functor C₁ C₂) Functor.Map

idᶠᵘⁿᶜᵗᵒʳ : ∀{C} → (C →ᶠᵘⁿᶜᵗᵒʳ C)
idᶠᵘⁿᶜᵗᵒʳ = intro(functor Fn.id Fn.id) Fn.id
