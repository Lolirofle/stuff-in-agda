module Structure.Operator.Ring.Homomorphism where

import      Lvl
open import Logic
open import Logic.Predicate
open import Structure.Function
open import Structure.Function.Multi
open import Structure.Setoid.WithLvl
open import Structure.Operator.Ring
open import Type

record Homomorphism
  {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂}
  {X : Type{ℓ₁}} ⦃ _ : Equiv{ℓₑ₁}(X) ⦄ {_+X_ _⋅X_ : X → X → X} (structureₗ : Ring(_+X_)(_⋅X_))
  {Y : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(Y) ⦄ {_+Y_ _⋅Y_ : Y → Y → Y} (structureᵣ : Ring(_+Y_)(_⋅Y_))
  (f : X → Y)
  : Stmt{ℓ₁ Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓₑ₂} where

  constructor intro

  𝟏ₗ = Ring.𝟏(structureₗ)
  𝟏ᵣ = Ring.𝟏(structureᵣ)

  field
    ⦃ function ⦄     : Function(f)
    ⦃ preserve-[+] ⦄ : Preserving₂(f)(_+X_)(_+Y_)
    ⦃ preserve-[⋅] ⦄ : Preserving₂(f)(_⋅X_)(_⋅Y_)
    ⦃ preserve-𝟏 ⦄   : Preserving₀(f)(𝟏ₗ)(𝟏ᵣ)

record Antihomomorphism
  {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂}
  {X : Type{ℓ₁}} ⦃ _ : Equiv{ℓₑ₁}(X) ⦄ {_+X_ _⋅X_ : X → X → X} (structureₗ : Ring(_+X_)(_⋅X_))
  {Y : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(Y) ⦄ {_+Y_ _⋅Y_ : Y → Y → Y} (structureᵣ : Ring(_+Y_)(_⋅Y_))
  (f : X → Y)
  : Stmt{ℓ₁ Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓₑ₂} where

  constructor intro

  𝟏ₗ = Ring.𝟏(structureₗ)
  𝟏ᵣ = Ring.𝟏(structureᵣ)

  field
    ⦃ function ⦄         : Function(f)
    ⦃ preserve-[+] ⦄     : Preserving₂(f)(_+X_)(_+Y_)
    ⦃ antipreserve-[⋅] ⦄ : ∀{x y} → (f(x ⋅X y) ≡ f(y) ⋅Y f(x))
    ⦃ preserve-𝟏 ⦄       : Preserving₀(f)(𝟏ₗ)(𝟏ᵣ)

_→ʳⁱⁿᵍ_ : ∀{ℓₗ ℓₗₑ ℓᵣ ℓᵣₑ} → RingObject{ℓₗ}{ℓₗₑ} → RingObject{ℓᵣ}{ℓᵣₑ} → Type
A →ʳⁱⁿᵍ B = ∃(Homomorphism(RingObject.ring A)(RingObject.ring B))
