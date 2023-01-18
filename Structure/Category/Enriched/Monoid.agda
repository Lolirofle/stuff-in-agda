open import Structure.Category
open import Structure.Category.Monoidal

-- A monoid in a category (operators and elements are defined using morphisms).
-- A generalization of the usual set definition of monoids (this type of generalization is called enrichment).
-- Also called: Enriched monoid, internal monoid, monoid object.
module Structure.Category.Enriched.Monoid
  {ℓₒ ℓₘ ℓₑ}
  (C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ})
  ⦃ M : Monoidalᶜᵃᵗ(C) ⦄
  where

open import Logic.Predicate
import      Lvl
open import Structure.Setoid
open import Type

open CategoryObject(C) renaming (Object to Objectₘ ; Morphism to Morphismₘ ; _∘_ to _∘ₘ_ ; id to idₘ)
open ArrowNotation renaming (_⟶_ to _⟶ₘ_)
open Monoidalᶜᵃᵗ(M) renaming (unitObject to 𝟏)

record Signature(M : Objectₘ) : Type{ℓₘ} where
  constructor _,_
  field
    ▫  : (M ⊗ M) ⟶ₘ M
    id : 𝟏 ⟶ₘ M

record Conditions {M : Objectₘ} (signature : Signature(M)) : Type{ℓₑ} where
  constructor intro
  open Signature(signature)
  field
    associativity-condition : ▫ ∘ₘ (idₘ <⊗> ▫) ∘ₘ α(M)(M)(M) ≡ ▫ ∘ₘ (▫ <⊗> idₘ)
    unitalityₗ-condition : ▫ ∘ₘ (id <⊗> idₘ) ≡ υₗ(M)
    unitalityᵣ-condition : ▫ ∘ₘ (idₘ <⊗> id) ≡ υᵣ(M)

module _ (M : Objectₘ) where
  Monoid : Type
  Monoid = ∃(Conditions{M})
module Monoid{M} (monoid : Monoid(M)) where
  open Signature([∃]-witness monoid) public
  open Conditions([∃]-proof monoid) public

MonoidObject : Type
MonoidObject = ∃(Monoid)
