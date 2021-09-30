module Structure.Operator.Ring.Homomorphism where

import      Lvl
open import Logic
open import Logic.Predicate
open import Structure.Function
open import Structure.Function.Multi
open import Structure.Setoid
open import Structure.Operator.Ring using (RingObject)
open import Type

module Ring where
  open Structure.Operator.Ring

  record Homomorphism
    {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂ ℓₙ₀₁ ℓₙ₀₂}
    {X : Type{ℓ₁}} ⦃ _ : Equiv{ℓₑ₁}(X) ⦄ {_+X_ _⋅X_ : X → X → X} (structureₗ : Ring(_+X_)(_⋅X_) {ℓₙ₀₁})
    {Y : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(Y) ⦄ {_+Y_ _⋅Y_ : Y → Y → Y} (structureᵣ : Ring(_+Y_)(_⋅Y_) {ℓₙ₀₂})
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
    {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂ ℓₙ₀₁ ℓₙ₀₂}
    {X : Type{ℓ₁}} ⦃ _ : Equiv{ℓₑ₁}(X) ⦄ {_+X_ _⋅X_ : X → X → X} (structureₗ : Ring(_+X_)(_⋅X_) {ℓₙ₀₁})
    {Y : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(Y) ⦄ {_+Y_ _⋅Y_ : Y → Y → Y} (structureᵣ : Ring(_+Y_)(_⋅Y_) {ℓₙ₀₂})
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

_→ʳⁱⁿᵍ_ : ∀{ℓₗ ℓₗₑ ℓₗₙ₀ ℓᵣ ℓᵣₑ ℓᵣₙ₀} → RingObject{ℓₗ}{ℓₗₑ}{ℓₗₙ₀} → RingObject{ℓᵣ}{ℓᵣₑ}{ℓᵣₙ₀} → Type
A →ʳⁱⁿᵍ B = ∃(Ring.Homomorphism(RingObject.ring A)(RingObject.ring B))

module SemiRg where
  open Structure.Operator.Ring

  record Homomorphism
    {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂ ℓₙ₀₁ ℓₙ₀₂}
    {X : Type{ℓ₁}} ⦃ _ : Equiv{ℓₑ₁}(X) ⦄ {_+X_ _⋅X_ : X → X → X} (structureₗ : Ring(_+X_)(_⋅X_) {ℓₙ₀₁})
    {Y : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(Y) ⦄ {_+Y_ _⋅Y_ : Y → Y → Y} (structureᵣ : Ring(_+Y_)(_⋅Y_) {ℓₙ₀₂})
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
    {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂ ℓₙ₀₁ ℓₙ₀₂}
    {X : Type{ℓ₁}} ⦃ _ : Equiv{ℓₑ₁}(X) ⦄ {_+X_ _⋅X_ : X → X → X} (structureₗ : Ring(_+X_)(_⋅X_) {ℓₙ₀₁})
    {Y : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(Y) ⦄ {_+Y_ _⋅Y_ : Y → Y → Y} (structureᵣ : Ring(_+Y_)(_⋅Y_) {ℓₙ₀₂})
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
