open import Structure.Categorical.Properties
open import Structure.Category
open import Structure.Category.Monoidal
open import Structure.Category.Monoidal.Diagonal

-- TODO: Not sure about this definition of an enriched group. I just made up something based on the definition of a monoid
-- Also called: Enriched group, internal group, group object.
module Structure.Category.Enriched.Group
  {ℓₒ ℓₘ ℓₑ}
  (C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ})
    (let open CategoryObject(C) renaming (Object to Objectₘ ; Morphism to Morphismₘ ; _∘_ to _∘ₘ_ ; id to idₘ))
    (let open ArrowNotation renaming (_⟶_ to _⟶ₘ_))
  ⦃ monoidal : Monoidalᶜᵃᵗ(C) ⦄
    (let open Monoidalᶜᵃᵗ(monoidal) renaming (unitObject to 𝟏))
  ⦃ diagonal : Diagonal ⦄
    (let open Diagonal(diagonal))
  where

open import Logic.Predicate
import      Lvl
open import Structure.Setoid
open import Type

record Signature(M : Objectₘ) : Type{ℓₘ} where
  constructor _,_
  field
    ▫   : (M ⊗ M) ⟶ₘ M
    inv : M ⟶ₘ M
    id  : 𝟏 ⟶ₘ M

record Conditions {M : Objectₘ} (signature : Signature(M)) : Type{ℓₑ} where
  constructor intro
  open Signature(signature)
  field
    associativity-condition : ▫ ∘ₘ (idₘ <⊗> ▫) ∘ₘ α(M)(M)(M) ≡ ▫ ∘ₘ (▫ <⊗> idₘ)
    inverseₗ-condition      : ▫ ∘ₘ (inv <⊗> idₘ) ∘ₘ diag(M) ≡ idₘ
    inverseᵣ-condition      : ▫ ∘ₘ (idₘ <⊗> inv) ∘ₘ diag(M) ≡ idₘ
    unitalityₗ-condition    : ▫ ∘ₘ (id <⊗> idₘ) ≡ υₗ(M)
    unitalityᵣ-condition    : ▫ ∘ₘ (idₘ <⊗> id) ≡ υᵣ(M)
