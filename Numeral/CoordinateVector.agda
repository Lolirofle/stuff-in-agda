module Numeral.CoordinateVector {ℓ} where

import      Lvl
open import Data.Boolean
open import Functional
open import Numeral.FiniteStrict
open import Numeral.FiniteStrict.Bound
open import Numeral.FiniteStrict.Oper
open import Numeral.FiniteStrict.Oper.Comparisons
open import Numeral.Natural
open import Type{ℓ}

-- Data in 1-dimensional finite space (Implies bounded).
-- Like a homogenous tuple or a fixed-size list.
record Vector (d : ℕ) (T : Type) : Type where
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

-- The first element of a non-empty vector
head : ∀{T}{d} → Vector(𝐒(d))(T) → T
head(v) = Vector.proj(v)(𝟎)

-- The list without the first element of a non-empty vector
tail : ∀{T}{d} → Vector(𝐒(d))(T) → Vector(d)(T)
Vector.proj(tail{_}{𝟎}   (v))()
Vector.proj(tail{_}{𝐒(_)}(v))(i) = Vector.proj(v)(𝐒(i))

-- The list without the first element if there were any
tail₀ : ∀{T}{d} → Vector(d)(T) → Vector(Numeral.Natural.𝐏(d))(T)
tail₀{_}{𝟎}    = id
tail₀{_}{𝐒(_)} = tail

-- Applies a function on every value of the vector
map : ∀{A B} → (A → B) → ∀{d} → Vector(d)(A) → Vector(d)(B)
Vector.proj(map f(v))(i) = f(Vector.proj(v)(i))

-- Applies a binary operation on every pair of values, each from 2 vectors
-- Example:
--   lift-binOp(_+_) [1,2,3] [10,20,30] = [1+10 , 2+20 , 3+30] = [11,22,33]
lift-binOp : ∀{A B C}{d} → (A → B → C) → Vector(d)(A) → Vector(d)(B) → Vector(d)(C)
Vector.proj(lift-binOp(_▫_) (v₁)(v₂))(i) = Vector.proj(v₁)(i) ▫ Vector.proj(v₂)(i)

-- Example:
--   reduceₗ (_▫_) (0) [1,2,3,4]
--   = (((0 ▫ 1) ▫ 2) ▫ 3) ▫ 4
reduceₗ : ∀{X Y : Type} → (Y → X → Y) → Y → ∀{d} → Vector(d)(X) → Y
reduceₗ (_▫_) (init) {𝟎}    (v) = init
reduceₗ (_▫_) (init) {𝐒(d)} (v) = reduceₗ (_▫_) (init ▫ (head v)) {d} (tail v)

-- Example:
--   reduceᵣ (_▫_) (0) [1,2,3,4]
--   = 0 ▫ (1 ▫ (2 ▫ (3 ▫ 4)))
reduceᵣ : ∀{X Y : Type} → (X → Y → Y) → Y → ∀{d} → Vector(d)(X) → Y
reduceᵣ (_▫_) (init) {𝟎}    (v) = init
reduceᵣ (_▫_) (init) {𝐒(d)} (v) = (head v) ▫ (reduceᵣ (_▫_) (init) {d} (tail v))

-- Example:
--   reduce₀ᵣ (_▫_) [1,2,3,4]
--   = 1 ▫ (2 ▫ (3 ▫ 4))
reduce₀ᵣ : ∀{X : Type} → (X → X → X) → ∀{d} → Vector(𝐒(d))(X) → X
reduce₀ᵣ (_▫_) {𝟎}    (v) = head v
reduce₀ᵣ (_▫_) {𝐒(d)} (v) = (head v) ▫ (reduce₀ᵣ (_▫_) (tail v))

-- A vector filled with multiple copies of a single element
fill : ∀{T}{d} → T → Vector(d)(T)
Vector.proj(fill(elem)) = const(elem)

-- A vector with an additional element at the beginning
prepend : ∀{T}{d} → T → Vector(d)(T) → Vector(𝐒(d))(T)
Vector.proj(prepend(x)(_)) (𝟎)    = x
Vector.proj(prepend(_)(v)) (𝐒(n)) = Vector.proj(v) (n)

count : ∀{T}{d} → (T → Bool) → Vector(d)(T) → ℕ
count {_}{𝟎}    (f)(v) = 𝟎
count {_}{𝐒(n)} (f)(v) = if f(head v) then 𝐒(next) else next where
  next = count {_}{n} (f)(tail v)

-- A vector without the element at the specified index
-- TODO: Implement Numeral.FiniteStrict.Bound.bound-𝐏
-- without : ∀{T}{d} → 𝕟(𝐒(d)) → Vector(𝐒(d))(T) → Vector(d)(T)
-- Vector.proj (without {_}{𝐒(_)} (𝟎)   (v)) (i) = Vector.proj(v)(𝐒(i))
-- Vector.proj (without {_}{𝐒(_)} (𝐒(n))(v)) (i) = if(i ≤? n) then Vector.proj(v)(𝐒(i)) else Vector.proj(v)(bound-𝐏(i))

-- postpend : ∀{T}{d} → T → Vector(d)(T) → Vector(𝐒(d))(T)
-- Vector.proj(postpend{_}{d} (x)(_)) (n) = if (n ≡? d) then x else Vector.proj(v)(n)

-- concat : ∀{T}{d₁ d₂} → Vector(d₁)(T) → Vector(d₂)(T) → Vector(d₁ + d₂)(T)
-- Vector.proj(concat(v₁)(v₂)) (n) with (n < d₁ ≡ 𝑇)
-- ... () = Vector.proj(v₁) (n)
-- ... () = Vector.proj(v₂) (n)

-- take / truncate
