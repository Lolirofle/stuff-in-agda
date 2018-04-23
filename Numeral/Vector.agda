module Numeral.Vector {ℓ} where

import      Lvl
open import Functional
open import Numeral.FiniteStrict
open        Numeral.FiniteStrict.Theorems
open import Numeral.Natural
open import Type{ℓ}

-- Data in 1-dimensional finite space (Implies bounded).
-- Like a data list.
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

head : ∀{T}{d} → Vector(𝐒(d))(T) → T
head(v) = Vector.proj(v)(𝟎)

tail : ∀{T}{d} → Vector(𝐒(d))(T) → Vector(d)(T)
Vector.proj(tail{_}{𝟎}   (v))()
Vector.proj(tail{_}{𝐒(_)}(v))(i) = Vector.proj(v)(𝐒(i))

tail₀ : ∀{T}{d} → Vector(d)(T) → Vector(Numeral.Natural.𝐏(d))(T)
tail₀{_}{𝟎}    = id
tail₀{_}{𝐒(_)} = tail

map : ∀{A B} → (A → B) → ∀{d} → Vector(d)(A) → Vector(d)(B)
Vector.proj(map f(v))(i) = f(Vector.proj(v)(i))

lift-binOp : ∀{A B C}{d} → (A → B → C) → Vector(d)(A) → Vector(d)(B) → Vector(d)(C)
Vector.proj(lift-binOp(_▫_) (v₁)(v₂))(i) = Vector.proj(v₁)(i) ▫ Vector.proj(v₂)(i)

reduceₗ : ∀{X Y : Type} → (Y → X → Y) → Y → ∀{d} → Vector(d)(X) → Y
reduceₗ (_▫_) (init) {𝟎}    (v) = init
reduceₗ (_▫_) (init) {𝐒(d)} (v) = reduceₗ (_▫_) (init ▫ (head v)) {d} (tail v)

reduceᵣ : ∀{X Y : Type} → (X → Y → Y) → Y → ∀{d} → Vector(d)(X) → Y
reduceᵣ (_▫_) (init) {𝟎}    (v) = init
reduceᵣ (_▫_) (init) {𝐒(d)} (v) = (head v) ▫ (reduceᵣ (_▫_) (init) {d} (tail v))

reduce₀ᵣ : ∀{X : Type} → (X → X → X) → ∀{d} → Vector(𝐒(d))(X) → X
reduce₀ᵣ (_▫_) {𝟎}    (v) = head v
reduce₀ᵣ (_▫_) {𝐒(d)} (v) = (head v) ▫ (reduce₀ᵣ (_▫_) (tail v))

fill : ∀{T}{d} → T → Vector(d)(T)
Vector.proj(fill(elem)) = const(elem)

{-
record Vector (T : Type{ℓ}) (d : ℕ) : Type{𝐒(ℓ)} where
  constructor vec
  field
    Element : Type{ℓ}
    proj : ℕfin(d) → Element
-}
