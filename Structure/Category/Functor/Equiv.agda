module Structure.Category.Functor.Equiv where

open import Functional.Equals
open import Logic
import      Lvl
open import Sets.Setoid
open import Structure.Category
open import Structure.Category.Functor

module _
  {ℓₒₗ ℓₘₗ ℓₒᵣ ℓₘᵣ : Lvl.Level}
  {Objₗ : Set(ℓₒₗ)}
  {Objᵣ : Set(ℓₒᵣ)}
  ⦃ obj-equivᵣ : Equiv(Objᵣ) ⦄
  {Morphismₗ : Objₗ → Objₗ → Set(ℓₘₗ)}
  ⦃ morphism-equivₗ : ∀{x y} → Equiv(Morphismₗ x y) ⦄
  {Morphismᵣ : Objᵣ → Objᵣ → Set(ℓₘᵣ)}
  ⦃ morphism-equivᵣ : ∀{x y} → Equiv(Morphismᵣ x y) ⦄
  (Categoryₗ : Category(Morphismₗ))
  (Categoryᵣ : Category(Morphismᵣ))
  where

  record _≡F_ (F₁ : Functor(Categoryₗ)(Categoryᵣ)) (F₂ : Functor(Categoryₗ)(Categoryᵣ)) : Stmt{ℓₒₗ Lvl.⊔ ℓₘₗ Lvl.⊔ ℓₒᵣ Lvl.⊔ ℓₘᵣ} where
    constructor intro
    field
      functor : Functor.functor(F₁) ⊜ Functor.functor(F₂)
      map     : ∀{x y} → Functor.map(F₁){x}{y} ⊜ Functor.map(F₂){x}{y} -- TODO: The type of the morphisms differs because of different `functor`, so (homogenous) equaliy does not work
