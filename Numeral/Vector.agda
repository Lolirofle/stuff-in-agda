module Numeral.Vector {ℓ} where

import      Lvl
open import Functional
open import Numeral.Finite
open        Numeral.Finite.Theorems
open import Numeral.Natural
open import Type{ℓ}

-- Data in 1-dimensional finite space (Implies bounded).
-- Like a data list.
record Vector (d : ℕ) (T : Type) : Type where
  constructor vec
  field
    -- Projection of a vector
    -- A cell in the vector
    proj : ℕfin(d) → T

  -- Type of elements in the vector
  Element : Type
  Element = T

  -- The maximum number of dimensions of a space that the vector can describe points in
  dim : ℕ
  dim = d

map : ∀{A B}{d} → (A → B) → Vector(d)(A) → Vector(d)(B)
Vector.proj(map f(v))(i) = f(Vector.proj(v)(i))

lift-binOp : ∀{A B C}{d} → (A → B → C) → Vector(d)(A) → Vector(d)(B) → Vector(d)(C)
Vector.proj(lift-binOp(_▫_) (v₁)(v₂))(i) = Vector.proj(v₁)(i) ▫ Vector.proj(v₂)(i)

-- TODO: reduce

{-
record Vector (T : Type{ℓ}) (d : ℕ) : Type{𝐒(ℓ)} where
  constructor vec
  field
    Element : Type{ℓ}
    proj : ℕfin(d) → Element
-}
