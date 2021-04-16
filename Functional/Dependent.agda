module Functional.Dependent where

import      Lvl
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level

-- Function type as a function
_→ᶠ_ : (X : Type{ℓ₁}) → (Type{ℓ₁} → Type{ℓ₂}) → Type{ℓ₁ Lvl.⊔ ℓ₂}
X →ᶠ Y = X → Y(X)
infixl 30 _→ᶠ_

module _ where
  private variable X : Type{ℓ}
  private variable Y : X → Type{ℓ}
  private variable Z : ∀{x : X} → Y(x) → Type{ℓ}

  apply : (x : X) → ((x : X) → Y(x)) → Y(x)
  apply(x)(f) = f(x)
  {-# INLINE apply #-}

  const : (∀{x : X} → Y(x)) → ((x : X) → Y(x))
  const y _ = y
  {-# INLINE const #-}

  _$_ : ((x : X) → Y(x)) → (x : X) → Y(x)
  f $ x = f(x)
  {-# INLINE _$_ #-}
  infixr 0 _$_

  _⩺_ : (x : X) → ((x : X) → Y(x)) → Y(x)
  x ⩺ f = f(x)
  {-# INLINE _⩺_ #-}
  infixl 10000 _⩺_

  _⩹_ : ((x : X) → Y(x)) → (x : X) → Y(x)
  f ⩹ x = f(x)
  {-# INLINE _⩹_ #-}
  infixl 10000 _⩹_

  _∘ᵢₘₚₗ_ : (∀{x : X}{y : Y(x)} → Z{x}(y)) → (g : ∀{x : X} → Y(x)) → (∀{x : X} → Z(g{x}))
  (f ∘ᵢₘₚₗ g){x} = f{x}{g{x}}
  infixl 10000 _∘ᵢₘₚₗ_

  _∘ᵢₙₛₜ_ : (⦃ x : X ⦄ ⦃ y : Y(x) ⦄ → Z{x}(y)) → (g : ⦃ x : X ⦄ → Y(x)) → (⦃ x : X ⦄ → Z(g ⦃ x ⦄))
  (f ∘ᵢₙₛₜ g) ⦃ x ⦄ = f ⦃ x ⦄ ⦃ g ⦃ x ⦄ ⦄
  infixl 10000 _∘ᵢₙₛₜ_

  _∘ₛ_ : ((x : X) → (y : Y(x)) → Z{x}(y)) → (g : (x : X) → Y(x)) → ((x : X) → Z(g(x)))
  (f ∘ₛ g)(x) = f(x)(g(x))
  {-# INLINE _∘ₛ_ #-}
  infixl 10000 _∘ₛ_

  _∘_ : (∀{x : X} → (y : Y(x)) → Z{x}(y)) → (g : (x : X) → Y(x)) → ((x : X) → Z(g(x)))
  _∘_ f = (const f) ∘ₛ_
  {-# INLINE _∘_ #-}
  infixl 10000 _∘_

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
  {-# INLINE swap #-}

{- TODO: Agda errors
module _ where
  private variable X₁ : Type{ℓ}
  private variable X₂ : X₁ → Type{ℓ}
  private variable Y₁ : ∀{x₁ : X₁} → X₂(x₁) → Type{ℓ}
  private variable Y₂ : ∀{x₁ : X₁}{x₂ : X₂(x₁)} → Y₁{x₁}(x₂) → Type{ℓ}
  private variable Z : ∀{x₁ : X₁}{x₂ : X₂(x₁)}{y₁ : Y₁{x₁}(x₂)} → (Y₂{x₁}{x₂}(y₁)) → Type{ℓ}

  pointwise₂,₁' : (∀{x₁ : X₁} → (x₂ : X₂(x₁)) → {y₁ : Y₁(x₂)} → (y₂ : Y₂(y₁)) → Z{x₁}{x₂}{y₁}(y₂)) → (f : (x₁ : X₁) → X₂(x₁)) → (g : ∀{x₁}{x₂} → (y₁ : Y₁{x₁}(x₂)) → Y₂{x₁}{x₂}(y₁)) → ((x₁ : X₁) → (y₁ : Y₁{x₁}(f(x₁))) → Z{x₁}{f(x₁)}{y₁}(g(y₁)))
-}
{-
module _ where
  private variable X₁ : Type{ℓ}
  private variable X₂ : X₁ → Type{ℓ}
  private variable Y₁ : ∀{x₁ : X₁} → X₂(x₁) → Type{ℓ}
  private variable Y₂ : ∀{x₁ : X₁}{x₂ : X₂(x₁)} → Y₁{x₁}(x₂) → Type{ℓ}
  private variable Z : ∀{x₁ : X₁}{x₂ : X₂(x₁)}{y₁ : Y₁{x₁}(x₂)} → Type{ℓ}

  pointwise₂,₁' : ∀{x₁ : X₁} → (x₂ : X₂(x₁)) → {y₁ : Y₁(x₂)} → (y₂ : Y₂(y₁)) → Z{x₁}{x₂}{y₁}
-}

module _ where
  private variable A : Type{ℓ}
  private variable B : A → Type{ℓ}
  private variable C : ∀{a : A} → B(a) → Type{ℓ}
  private variable D : ∀{a : A}{b : B(a)} → (C{a}(b)) → Type{ℓ}
  private variable E : ∀{a : A}{b : B(a)}{c : C{a}(b)} → D{a}{b}(c) → Type{ℓ}
  private variable F : ∀{a : A}{b : B(a)}{c : C{a}(b)}{d : D{a}{b}(c)} → E{a}{b}{c}(d) → Type{ℓ}

  -- Alternative definition: (f ∘₂ g) a b = f(g a b)
  _∘₂_ : (∀{a : A}{b : B(a)} → (c : C{a}(b)) → D{a}{b}(c)) → (g : ∀(a)(b) → C{a}(b)) → (∀(a)(b) → D(g a b))
  _∘₂_ f = (f ∘_) ∘_
  {-# INLINE _∘₂_ #-}

  -- Alternative definition: (f ∘₂ₛ g) x y = f a b (g a b)
  _∘₂ₛ_ : ((a : A) → (b : B(a)) → (c : C{a}(b)) → D{a}{b}(c)) → (g : ∀(a)(b) → C{a}(b)) → (∀(a)(b) → D(g a b))
  _∘₂ₛ_ f = ((_∘ₛ_) ∘ f) ∘ₛ_
  {-# INLINE _∘₂ₛ_ #-}

  -- Alternative definition: (f ∘₂ g) a b c = f(g a b c)
  _∘₃_ : (∀{a : A}{b : B(a)}{c : C{a}(b)} → (d : D{a}{b}(c)) → E{a}{b}{c}(d)) → (g : ∀(a)(b)(c) → D{a}{b}(c)) → (∀(a)(b)(c) → E(g a b c))
  _∘₃_ f = (f ∘₂_) ∘_
  {-# INLINE _∘₃_ #-}

  -- Alternative definition: (f ∘₃ₛ g) a b c = f a b c (g a b c)
  _∘₃ₛ_ : (∀(a : A)(b : B(a))(c : C{a}(b)) → (d : D{a}{b}(c)) → E{a}{b}{c}(d)) → (g : ∀(a)(b)(c) → D{a}{b}(c)) → (∀(a)(b)(c) → E(g a b c))
  _∘₃ₛ_ f = ((_∘₂ₛ_) ∘ f) ∘ₛ_
  {-# INLINE _∘₃ₛ_ #-}

  -- Alternative definition: (f ∘₄ g) a b c d = f(g a b c d)
  _∘₄_ : (∀{a : A}{b : B(a)}{c : C{a}(b)}{d : D{a}{b}(c)} → (e : E{a}{b}{c}(d)) → F{a}{b}{c}{d}(e)) → (g : ∀(a)(b)(c)(d) → E{a}{b}{c}(d)) → (∀(a)(b)(c)(d) → F(g a b c d))
  _∘₄_ f = (f ∘₃_) ∘_
  {-# INLINE _∘₄_ #-}

  -- Alternative definition: (f ∘₄ₛ g) a b c d = f a b c d (g a b c d)
  _∘₄ₛ_ : (∀(a : A)(b : B(a))(c : C{a}(b))(d : D{a}{b}(c)) → (e : E{a}{b}{c}(d)) → F{a}{b}{c}{d}(e)) → (g : ∀(a)(b)(c)(d) → E{a}{b}{c}(d)) → (∀(a)(b)(c)(d) → F(g a b c d))
  _∘₄ₛ_ f = ((_∘₃ₛ_) ∘ f) ∘ₛ_
  {-# INLINE _∘₄ₛ_ #-}

  -- Alternative definition: pointwise₂,₁(_▫_) f g a = f(a) ▫ g(a)
  pointwise₂,₁ : (∀{a : A} → (b : B(a)) → (c : C{a}(b)) → D{a}{b}(c)) → (f : (a : A) → B(a)) → (g : (a : A) → C{a}(f(a))) → (a : A) → D{a}{f(a)}(g(a))
  pointwise₂,₁(_▫_) = ((_∘ₛ_) ∘ ((_▫_) ∘_))
  {-# INLINE pointwise₂,₁ #-}

  -- Alternative definition: pointwise₂,₂(_▫_) f g a b = (f a b) ▫ (g a b)
  pointwise₂,₂ : (∀{a : A}{b : B(a)} → (c : C{a}(b)) → (d : D{a}{b}(c)) → E{a}{b}{c}(d)) → (f : (a : A) → (b : B(a)) → C{a}(b)) → (g : (a : A) → (b : B(a)) → D{a}{b}(f a b)) → (a : A) → (b : B(a)) → E{a}{b}{f a b}(g a b)
  pointwise₂,₂(_▫_) = pointwise₂,₁(pointwise₂,₁(_▫_))
  {-# INLINE pointwise₂,₂ #-}

  -- Alternative definition: pointwise₂,₃(_▫_) f g a b c = (f a b c) ▫ (g a b c)
  pointwise₂,₃ : (∀{a : A}{b : B(a)}{c : C{a}(b)} → (d : D{a}{b}(c)) → (e : E{a}{b}{c}(d)) → F{a}{b}{c}{d}(e)) → (f : (a : A) → (b : B(a)) → (c : C{a}(b)) → D{a}{b}(c)) → (g : (a : A) → (b : B(a)) → (c : C{a}(b)) → E{a}{b}(f a b c)) → (a : A) → (b : B(a)) → (c : C{a}(b)) → F{a}{b}{c}{f a b c}(g a b c)
  pointwise₂,₃(_▫_) = pointwise₂,₁(pointwise₂,₂(_▫_))
  {-# INLINE pointwise₂,₃ #-}
