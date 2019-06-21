module Structure.Arithmetic {ℓₗ}{ℓₒ} where

import      Lvl
open import Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ}
open import Relator.Equals{ℓₗ Lvl.⊔ ℓₒ}{ℓₒ}
open import Structure.Relator.Ordering{ℓₗ}{ℓₒ}
open import Structure.Function.Domain{ℓₗ}
open import Type

record Language (T : Type{ℓₒ}) : Type{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
  field
    𝟎 : T
    𝐒 : T → T

    _<_ : T → T → Stmt

record Minimal (T : Type{ℓₒ}) ⦃ _ : Language(T) ⦄ : Type{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
  open Language ⦃ ... ⦄
  open From-[<][≡] {T} (_<_) (_≡_)

  field
    [𝐒]-positivity  : ∀{x : T} → (𝐒(x) ≢ 𝟎)
    [𝐒]-injectivity : Injective{ℓₒ}{ℓₒ}{T}{T}(𝐒)

    [<][𝟎]ₗ : ∀{x : T} → (𝟎 < x) ↔ (x ≢ 𝟎)
    [<][𝟎]ᵣ : ∀{x : T} → (x ≥ 𝟎) -- Minimum in the order (TODO: Is (∀x. x≥0) neccessary? Which means (0<x)∨(0=x))
    [<][𝐒]ₗ : ∀{x y : T} → (𝐒(x) < y) ↔ ((x < y)∧(𝐒(x) ≢ y)) -- TODO: Also the definition of (_≤_)?
    [<][𝐒]ᵣ : ∀{x y : T} → (x < 𝐒(y)) ↔ (x ≤ y)

record Peano (T : Type{ℓₒ}) ⦃ _ : Language(T) ⦄ : Type{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
  open Language ⦃ ... ⦄

  field
   ⦃ minimal ⦄ : Minimal(T)

  field
    induction : ∀{P : T → Stmt} → P(𝟎) → (∀{x} → P(x) → P(𝐒(x))) → (∀{x} → P(x))

record Addition (T : Type{ℓₒ}) ⦃ _ : Language(T) ⦄ : Type{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
  open Language ⦃ ... ⦄

  field
    _+_ : T → T → T

  field
    [+]-base    : ∀{x : T} → (x + 𝟎 ≡ x)
    [+]-step    : ∀{x y : T} → (x + 𝐒(y) ≡ 𝐒(x + y))

record Multiplication (T : Type{ℓₒ}) ⦃ _ : Language(T) ⦄ ⦃ _ : Addition(T) ⦄ : Type{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
  open Language ⦃ ... ⦄
  open Addition ⦃ ... ⦄

  field
    _⋅_ : T → T → T

  field
    [⋅]-base    : ∀{x : T} → (x ⋅ 𝟎 ≡ 𝟎)
    [⋅]-step    : ∀{x y : T} → (x ⋅ 𝐒(y) ≡ (x ⋅ y) + x)
