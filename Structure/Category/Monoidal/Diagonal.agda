import      Lvl
open import Structure.Categorical.Properties
open import Structure.Category
open import Structure.Category.Monoidal

module Structure.Category.Monoidal.Diagonal
  {ℓₒ ℓₘ ℓₑ : Lvl.Level}
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} (let open CategoryObject(C)) (let open ArrowNotation)
  ⦃ M : Monoidalᶜᵃᵗ(C) ⦄           (let open Monoidalᶜᵃᵗ(M) renaming (productFunctor to ⊗ᶠᵘⁿᶜᵗᵒʳ ; unitObject to 𝟏))
  where

open        Structure.Categorical.Properties.Object using ()
open import Structure.Setoid
open import Type
import      Type.Properties.Singleton as Singleton

-- TODO: Is it possible to construct a comonoid from this?

{-
-- TODO: This was written before I found a name for it. There are actually some sources that describe this structure: https://ncatlab.org/nlab/show/diagonal+morphism https://ncatlab.org/nlab/show/monoidal%20category%20with%20diagonals https://ncatlab.org/nlab/show/diagonal+functor
record Diagonal ⦃ terminal : Object.Terminal(_⟶_)(𝟏) ⦄ : Type{ℓₒ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
  constructor intro
  field diag : ∀(x) → (x ⟶ (x ⊗ x))
  field
    identityₗ-condition : ∀{x} → ((unit(_⟶_)(x) <⊗> id) ∘ diag(x) ≡ υₗ⁻¹(x))
    identityᵣ-condition : ∀{x} → ((id <⊗> unit(_⟶_)(x)) ∘ diag(x) ≡ υᵣ⁻¹(x))
-}

open import Data.Tuple as Tuple using (_,_)
open import Data.Tuple.Category
import      Functional as Fn
open import Logic.Predicate
open import Structure.Category.Functor
import      Structure.Category.Functor.Functors
open        Structure.Category.Functor.Functors.Wrapped
open import Structure.Category.NaturalTransformation

open Functor ⦃ … ⦄

record Diagonal : Type{Lvl.𝐒(ℓₒ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ)} where
  constructor intro
  field diagᴺᵀ : idᶠᵘⁿᶜᵗᵒʳ →ᴺᵀ (⊗ᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.diag)

  diag : ∀(x) → (x ⟶ (x ⊗ x))
  diag = [∃]-witness diagᴺᵀ

  diag-natural : ∀{x y}{f} → (diag(y) ∘ f ≡ (f <⊗> f) ∘ diag(x))
  diag-natural = NaturalTransformation.natural([∃]-proof diagᴺᵀ)

  field
    unit-diag-unitorₗ-inverse-condition : (diag(𝟏) ∘ υₗ(𝟏) ≡ id)
    unit-diag-unitorᵣ-inverse-condition : (diag(𝟏) ∘ υᵣ(𝟏) ≡ id)
    unit-unitorₗ-diag-inverse-condition : (υₗ(𝟏) ∘ diag(𝟏) ≡ id)
    unit-unitorᵣ-diag-inverse-condition : (υᵣ(𝟏) ∘ diag(𝟏) ≡ id)

  {- TODO: Is it possible to prove these? Do they actually make sense?
  private open module MorphismEquiv{x}{y} = Equiv(morphism-equiv{x}{y}) using ()
  open import Syntax.Transitivity
  module _ ⦃ terminal : Object.Terminal(_⟶_)(𝟏) ⦄ where
    identityₗ-condition : ∀{x} → ((unit(_⟶_)(x) <⊗> id) ∘ diag(x) ≡ υₗ⁻¹(x))
    identityₗ-condition{x} =
      (unit(_⟶_)(x) <⊗> id) ∘ diag(x) 🝖[ _≡_ ]-[ {!!} ]
      υₗ⁻¹(x)                         🝖-end
    
    identityᵣ-condition : ∀{x} → ((id <⊗> unit(_⟶_)(x)) ∘ diag(x) ≡ υᵣ⁻¹(x))
  -}
