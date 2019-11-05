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
  {Categoryₗ : Category(Morphismₗ)}
  {Categoryᵣ : Category(Morphismᵣ)}
  where

  data _≡F_ : ∀{F₁ F₂} → Functor(Categoryₗ)(Categoryᵣ)(F₁) → Functor(Categoryₗ)(Categoryᵣ)(F₂) → Stmt{ℓₒₗ Lvl.⊔ ℓₘₗ Lvl.⊔ ℓₒᵣ Lvl.⊔ ℓₘᵣ} where
    intro : ∀{F : Objₗ → Objᵣ}{functor₁ functor₂ : Functor(Categoryₗ)(Categoryᵣ)(F)}{x y} → (Functor.map(functor₁){x}{y} ⊜ Functor.map(functor₂){x}{y}) → (functor₁ ≡F functor₂)
