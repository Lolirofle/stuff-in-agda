module Functional.Dependent where

import      Lvl
open import Type

infixl 30 _→ᶠ_

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level

-- Function type as a function
_→ᶠ_ : (X : Type{ℓ₁}) → (Type{ℓ₁} → Type{ℓ₂}) → Type{ℓ₁ Lvl.⊔ ℓ₂}
X →ᶠ Y = X → Y(X)

module _ where
  infixl 10000 _∘_
  infixl 10000 _⩺_
  infixl 10000 _⩹_
  infixr 0 _$_

  private variable X : Type{ℓ}
  private variable Y : X → Type{ℓ}
  private variable Z : ∀{x : X} → Y(x) → Type{ℓ}

  apply : (x : X) → ((x : X) → Y(x)) → Y(x)
  apply(x)(f) = f(x)

  const : (∀{x : X} → Y(x)) → ((x : X) → Y(x))
  const y _ = y

  _$_ : ((x : X) → Y(x)) → (x : X) → Y(x)
  f $ x = f(x)

  _⩺_ : (x : X) → ((x : X) → Y(x)) → Y(x)
  x ⩺ f = f(x)

  _⩹_ : ((x : X) → Y(x)) → (x : X) → Y(x)
  f ⩹ x = f(x)

  _∘_ : (∀{x : X} → (y : Y(x)) → Z{x}(y)) → (g : (x : X) → Y(x)) → ((x : X) → Z(g(x)))
  (f ∘ g)(x) = f{x}(g(x))

  _∘ᵢₘₚₗ_ : (∀{x : X}{y : Y(x)} → Z{x}(y)) → (g : ∀{x : X} → Y(x)) → (∀{x : X} → Z(g{x}))
  (f ∘ᵢₘₚₗ g){x} = f{x}{g{x}}

  _∘ᵢₙₛₜ_ : (⦃ x : X ⦄ ⦃ y : Y(x) ⦄ → Z{x}(y)) → (g : ⦃ x : X ⦄ → Y(x)) → (⦃ x : X ⦄ → Z(g ⦃ x ⦄))
  (f ∘ᵢₙₛₜ g) ⦃ x ⦄ = f ⦃ x ⦄ ⦃ g ⦃ x ⦄ ⦄

  _∘ₛ_ : ((x : X) → (y : Y(x)) → Z{x}(y)) → (g : (x : X) → Y(x)) → ((x : X) → Z(g(x)))
  (f ∘ₛ g)(x) = f(x)(g(x))

module _ where
  private variable X : Type{ℓ}
  private variable Y : X → Type{ℓ}
  private variable Z : ∀{x₁ x₂ : X} → Y(x₁) → Y(x₂) → Type{ℓ}

  _on₂_ : (f : ∀{x₁ x₂ : X} → (y₁ : Y(x₁)) → (y₂ : Y(x₂)) → Z{x₁}{x₂}(y₁)(y₂)) → (g : (x : X) → Y(x)) → ((x₁ : X) → (x₂ : X) → Z(g(x₁))(g(x₂)))
  ((_▫_) on₂ f)(y₁)(y₂) = f(y₁) ▫ f(y₂)

module _ where
  private variable X Y : Type{ℓ}
  private variable Z : X → Y → Type{ℓ}

  swap : ((x : X) → (y : Y) → Z(x)(y)) → ((y : Y) → (x : X) → Z(x)(y))
  swap f(y)(x) = f(x)(y)
