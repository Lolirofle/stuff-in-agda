module Numeral.CoordinateVector where

import      Lvl
open import Data.Boolean
open import Functional
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Finite.Oper
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Natural
open import Type

module _ {ℓ} where
  -- Data in 1-dimensional finite space (Implies bounded).
  -- Like a homogenous tuple or a fixed-size list.
  record Vector (d : ℕ) (T : Type{ℓ}) : Type{ℓ} where
    constructor vec
    field
      -- Projection of a vector
      -- A cell in the vector
      proj : 𝕟(d) → T

    -- Type of elements in the vector
    Element : Type
    Element = T

    -- The maximum number of dimensions of a space that the vector can describe points in
    dim : ℕ
    dim = d

module _ {ℓ} {T : Type{ℓ}} where
  -- The first element of a non-empty vector
  head : ∀{d} → Vector(𝐒(d))(T) → T
  head(v) = Vector.proj(v)(𝟎)

  -- The list without the first element of a non-empty vector
  tail : ∀{d} → Vector(𝐒(d))(T) → Vector(d)(T)
  Vector.proj(tail{𝟎}   (v))()
  Vector.proj(tail{𝐒(_)}(v))(i) = Vector.proj(v)(𝐒(i))

  -- The list without the first element if there were any
  tail₀ : ∀{d} → Vector(d)(T) → Vector(Numeral.Natural.𝐏(d))(T)
  tail₀{𝟎}    = id
  tail₀{𝐒(_)} = tail

  -- The last element of a non-empty vector
  last : ∀{d} → Vector(𝐒(d))(T) → T
  last(v) = Vector.proj(v)(maximum)

  -- The list without the last element if there were any
  withoutLast : ∀{d} → Vector(𝐒(d))(T) → Vector(d)(T)
  Vector.proj(withoutLast v)(i) = Vector.proj(v)(bound-𝐒(i))

module _ {ℓ₁ ℓ₂} {X : Type{ℓ₁}} {Y : Type{ℓ₂}} where
  -- Applies a function on every value of the vector
  map : (X → Y) → ∀{d} → Vector(d)(X) → Vector(d)(Y)
  Vector.proj(map f(v))(i) = f(Vector.proj(v)(i))

module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}} {Y : Type{ℓ₂}} {Z : Type{ℓ₃}} where
  -- Applies a binary operation on every pair of values, each from 2 vectors elementwise
  -- Example:
  --   map₂(_+_) [1,2,3] [10,20,30] = [1+10 , 2+20 , 3+30] = [11,22,33]
  map₂ : ∀{d} → (X → Y → Z) → Vector(d)(X) → Vector(d)(Y) → Vector(d)(Z)
  Vector.proj(map₂(_▫_) (v₁)(v₂))(i) = Vector.proj(v₁)(i) ▫ Vector.proj(v₂)(i)

module _ {ℓ₁ ℓ₂} {X : Type{ℓ₁}} {Y : Type{ℓ₂}} where
  -- Example:
  --   reduceₗ (_▫_) (0) [1,2,3,4]
  --   = (((0 ▫ 1) ▫ 2) ▫ 3) ▫ 4
  reduceₗ : (Y → X → Y) → Y → ∀{d} → Vector(d)(X) → Y
  reduceₗ (_▫_) (init) {𝟎}    (v) = init
  reduceₗ (_▫_) (init) {𝐒(d)} (v) = reduceₗ (_▫_) (init ▫ (head v)) {d} (tail v)

  -- Example:
  --   reduceᵣ (_▫_) (0) [1,2,3,4]
  --   = 0 ▫ (1 ▫ (2 ▫ (3 ▫ 4)))
  reduceᵣ : (X → Y → Y) → Y → ∀{d} → Vector(d)(X) → Y
  reduceᵣ (_▫_) (init) {𝟎}    (v) = init
  reduceᵣ (_▫_) (init) {𝐒(d)} (v) = (head v) ▫ (reduceᵣ (_▫_) (init) {d} (tail v))

module _ {ℓ} {T : Type{ℓ}} where
  -- Example:
  --   reduce₀ᵣ (_▫_) [1,2,3,4]
  --   = 1 ▫ (2 ▫ (3 ▫ 4))
  reduce₀ᵣ : (T → T → T) → ∀{d} → Vector(𝐒(d))(T) → T
  reduce₀ᵣ (_▫_) {𝟎}    (v) = head v
  reduce₀ᵣ (_▫_) {𝐒(d)} (v) = (head v) ▫ (reduce₀ᵣ (_▫_) (tail v))

  -- A vector filled with multiple copies of a single element
  fill : ∀{d} → T → Vector(d)(T)
  Vector.proj(fill(elem)) = const(elem)

  -- A vector with an additional element at the beginning
  prepend : ∀{d} → T → Vector(d)(T) → Vector(𝐒(d))(T)
  Vector.proj(prepend(x)(_)) (𝟎)    = x
  Vector.proj(prepend(_)(v)) (𝐒(n)) = Vector.proj(v) (n)

  count : ∀{d} → (T → Bool) → Vector(d)(T) → ℕ
  count {𝟎}    (f)(v) = 𝟎
  count {𝐒(n)} (f)(v) = if f(head v) then 𝐒(next) else next where
    next = count{n} (f)(tail v)

  -- A vector without the element at the specified index
  -- TODO: Implement Numeral.Finite.Bound.bound-𝐏
  -- without : ∀{T}{d} → 𝕟(𝐒(d)) → Vector(𝐒(d))(T) → Vector(d)(T)
  -- Vector.proj (without {_}{𝐒(_)} (𝟎)   (v)) (i) = Vector.proj(v)(𝐒(i))
  -- Vector.proj (without {_}{𝐒(_)} (𝐒(n))(v)) (i) = if(i ≤? n) then Vector.proj(v)(𝐒(i)) else Vector.proj(v)(bound-𝐏(i))

  -- postpend : ∀{T}{d} → T → Vector(d)(T) → Vector(𝐒(d))(T)
  -- Vector.proj(postpend{_}{d} (x)(_)) (n) = if (n ≡? d) then x else Vector.proj(v)(n)

  -- concat : ∀{T}{d₁ d₂} → Vector(d₁)(T) → Vector(d₂)(T) → Vector(d₁ + d₂)(T)
  -- Vector.proj(concat(v₁)(v₂)) (n) with (n < d₁ ≡ 𝑇)
  -- ... () = Vector.proj(v₁) (n)
  -- ... () = Vector.proj(v₂) (n)

  -- TODO: take / truncate
  -- TODO: Equality by function equality
