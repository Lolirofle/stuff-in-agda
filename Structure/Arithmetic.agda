module Structure.Arithmetic {ℓ} where

record Language (T : Set) : Set where
  field
    𝟎 : T
    𝐒 : T → T

    _+_ : T → T → T
    _⋅_ : T → T → T

    _<_ : T → T → Set

  _>_ : T → T → Set
  _>_ = _<_

record Minimal (T : Set) ⦃ _ : Language(T) ⦄ : Set where
  field
    [𝐒]-positivity  : ∀{x} → (𝐒(x) ≢ 𝟎)
    [𝐒]-injectivity : Injective(𝐒)

    [+]-base    : ∀{x} → (x + 𝟎 ≡ x)
    [+]-step    : ∀{x y} → (x + 𝐒(y) ≡ 𝐒(x + y))

    [⋅]-base    : ∀{x} → (x ⋅ 𝟎 ≡ 𝟎)
    [⋅]-step    : ∀{x y} → (x ⋅ 𝐒(y) ≡ (x ⋅ y) + x)

    [<]-minimum : ∀{x} → (x ≮ 0)
    [<][𝟎]      : ∀{x} → (𝟎 < x) ↔ (x ≢ 𝟎)
    [<][𝐒]₁     : ∀{x y} → (x < 𝐒(y)) ↔ ((x < y)∨(x ≡ y))
    [<][𝐒]₂     : ∀{x y} → (𝐒(x) < y) ↔ ((x < y)∧(𝐒(x) ≢ y))

record Peano (T : Set) ⦃ _ : Language(T) ⦄ : Set where
  field
    ⦃ minimal ⦄ : Minimal(T)

  field
    induction : ∀{P : T → Set} → P(𝟎) → (∀{x} → P(x) → P(𝐒(x))) → (∀{x} → P(x))
