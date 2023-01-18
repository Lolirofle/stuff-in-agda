module DependentFunctional where

import      Lvl
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level

module _ where
  private variable A B : Type{ℓ}
  private variable C : A → B → Type{ℓ}

  swap : ((a : A) → (b : B) → C(a)(b)) → ((b : B) → (a : A) → C(a)(b))
  swap f(b)(a) = f(a)(b)
  {-# INLINE swap #-}

module _ where
  private variable A : Type{ℓ}
  private variable B : A → Type{ℓ}
  private variable C : ∀{a : A} → B(a) → Type{ℓ}
  private variable D : ∀{a : A}{b : B(a)} → (C{a}(b)) → Type{ℓ}
  private variable E : ∀{a : A}{b : B(a)}{c : C{a}(b)} → D{a}{b}(c) → Type{ℓ}
  private variable F : ∀{a : A}{b : B(a)}{c : C{a}(b)}{d : D{a}{b}(c)} → E{a}{b}{c}(d) → Type{ℓ}

  _$_ : ((a : A) → B(a)) → (a : A) → B(a)
  f $ x = f(x)
  {-# INLINE _$_ #-}
  infixr 0 _$_

  _₴_ : (a : A) → ((a : A) → B(a)) → B(a)
  x ₴ f = f(x)
  {-# INLINE _₴_ #-}
  infixl 10000 _₴_
  apply = _₴_
  {-# INLINE apply #-}

  const : (∀{a : A} → B(a)) → ((a : A) → B(a))
  const y _ = y
  {-# INLINE const #-}

  constAlt : (a : A) → B(a) → A
  constAlt x _ = x
  {-# INLINE constAlt #-}

  _∘ᵢₘₚₗ_ : (∀{a : A}{b : B(a)} → C{a}(b)) → (g : ∀{a : A} → B(a)) → (∀{a : A} → C(g{a}))
  (f ∘ᵢₘₚₗ g){x} = f{x}{g{x}}
  infixl 10000 _∘ᵢₘₚₗ_

  _∘ᵢₙₛₜ_ : (⦃ a : A ⦄ ⦃ b : B(a) ⦄ → C{a}(b)) → (g : ⦃ a : A ⦄ → B(a)) → (⦃ a : A ⦄ → C(g ⦃ a ⦄))
  (f ∘ᵢₙₛₜ g) ⦃ x ⦄ = f ⦃ x ⦄ ⦃ g ⦃ x ⦄ ⦄
  infixl 10000 _∘ᵢₙₛₜ_

  _∘ₛ_ : ((a : A) → (b : B(a)) → C{a}(b)) → (g : (a : A) → B(a)) → ((a : A) → C(g(a)))
  (f ∘ₛ g)(x) = f(x)(g(x))
  {-# INLINE _∘ₛ_ #-}
  infixl 10000 _∘ₛ_

  _∘_ : (∀{a : A} → (b : B(a)) → C{a}(b)) → (g : (a : A) → B(a)) → ((a : A) → C(g(a)))
  _∘_ f = (const f) ∘ₛ_
  {-# INLINE _∘_ #-}
  infixl 10000 _∘_

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

module _ where
  private variable A : Type{ℓ}
  private variable B : A → Type{ℓ}
  private variable C₂ : ∀{a₁ a₂ : A} → B(a₁) → B(a₂) → Type{ℓ}
  private variable C₃ : ∀{a₁ a₂ a₃ : A} → B(a₁) → B(a₂) → B(a₃) → Type{ℓ}

  _on₂_ : (f : ∀{a₁ a₂ : A} → (b₁ : B(a₁)) → (b₂ : B(a₂)) → C₂{a₁}{a₂}(b₁)(b₂)) → (g : (a : A) → B(a)) → ((a₁ : A) → (a₂ : A) → C₂(g(a₁))(g(a₂)))
  ((_▫_) on₂ f)(b₁)(b₂) = f(b₁) ▫ f(b₂)

  _on₃_ : (f : ∀{a₁ a₂ a₃ : A} → (b₁ : B(a₁)) → (b₂ : B(a₂)) → (b₃ : B(a₃)) → C₃{a₁}{a₂}{a₃}(b₁)(b₂)(b₃)) → (g : (a : A) → B(a)) → ((a₁ : A) → (a₂ : A) → (a₃ : A) → C₃(g(a₁))(g(a₂))(g(a₃)))
  ((_▫_▫_) on₃ f)(b₁)(b₂)(b₃) = f(b₁) ▫ f(b₂) ▫ f(b₃)
