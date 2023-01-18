module Structure.Category.Adjunction where

import      Lvl
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Category
open import Structure.Category.Functor
import      Structure.Category.Functor.Functors as Functors
open import Structure.Category.NaturalTransformation
open import Type

private variable ℓ ℓₒ ℓₘ ℓₑ ℓₒ₁ ℓₘ₁ ℓₑ₁ ℓₒ₂ ℓₘ₂ ℓₑ₂ : Lvl.Level
private variable Obj : Type{ℓ}
private variable Morphism : Obj → Obj → Type{ℓ}

open Functors.Wrapped

module _
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}}
  {D : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}}
  (Fᶠᵘⁿᶜᵗᵒʳ@([∃]-intro F) : C →ᶠᵘⁿᶜᵗᵒʳ D)
  (Gᶠᵘⁿᶜᵗᵒʳ@([∃]-intro G) : D →ᶠᵘⁿᶜᵗᵒʳ C)
  where

  open CategoryObject ⦃ … ⦄
  open Category.ArrowNotation ⦃ … ⦄
  open Functor ⦃ … ⦄

  private instance _ = C
  private instance _ = D

  -- A weaker form of functor isomorphism.
  -- This states that F is left adjoint to G, or alternatively G is right adjoint to F.
  record Adjoint : Type{Lvl.𝐒(ℓₒ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ)} where
    constructor intro
    field
      Η : (Gᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ Fᶠᵘⁿᶜᵗᵒʳ) ←ᴺᵀ idᶠᵘⁿᶜᵗᵒʳ
      Ε : (Fᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ Gᶠᵘⁿᶜᵗᵒʳ) →ᴺᵀ idᶠᵘⁿᶜᵗᵒʳ

    η : ∀(x) → (G(F(x)) ⟵ x)
    η = [∃]-witness Η

    ε : ∀(x) → (F(G(x)) ⟶ x)
    ε = [∃]-witness Ε

    η-natural : ∀{x y}{f : x ⟶ y} → (η(y) ∘ f ≡ map(map(f)) ∘ η(x))
    η-natural = NaturalTransformation.natural([∃]-proof Η)

    ε-natural : ∀{x y}{f : x ⟶ y} → (ε(y) ∘ map(map f) ≡ f ∘ ε(x))
    ε-natural = NaturalTransformation.natural([∃]-proof Ε)

    field
      inverseₗ : ∀{x} → (ε(F(x)) ∘ map(η(x)) ≡ id)
      inverseᵣ : ∀{x} → (map(ε(x)) ∘ η(G(x)) ≡ id)
