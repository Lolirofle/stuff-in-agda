module Numeral.Matrix {ℓ} where

import      Lvl
open import Syntax.Number
open import Data
open import Numeral.Finite
open        Numeral.Finite.Theorems
open import Numeral.Natural
open import Numeral.Vector using (Vector)
open import Type{ℓ}

-- Data in 2-dimensional finite space (Implies bounded).
-- Like a data table.
record Matrix (s : ℕ ⨯ ℕ) (T : Type) : Type where
  constructor mat
  field
    -- Projection of a matrix
    -- A cell in the matrix
    proj : (ℕfin(Tuple.left(s)) ⨯ ℕfin(Tuple.right(s))) → T

  -- Type of elements in the matrix
  Element : Type
  Element = T

  -- Width of the matrix (Number of columns)
  width : ℕ
  width = Tuple.left(s)

  -- Height of the matrix (Number of rows)
  height : ℕ
  height = Tuple.right(s)

  -- Vector of a row in the matrix
  row : ℕfin(height) → Vector(width)(T)
  Vector.proj(row(y))(x) = proj(x , y)

  -- Vector of a column in the matrix
  col : ℕfin(width) → Vector(height)(T)
  Vector.proj(col(x))(y) = proj(x , y)

  -- Transpose (Reflection on main diagonal)
  ⬔_ : Matrix(height , width)(T)
  proj(⬔_)(x , y) = proj(y , x)

  module Rows where
    -- TODO: swap, map
  module Cols where

map : ∀{s}{A B} → (A → B) → Matrix(s)(A) → Matrix(s)(B) -- TODO: Same implementation in Vector.agda. Generalize. Maybe like in Haskell? With Applicative, Functor and stuff?
Matrix.proj(map f(m))(x , y) = f(Matrix.proj(m)(x , y))

lift-binOp : ∀{A B C}{s} → (A → B → C) → Matrix(s)(A) → Matrix(s)(B) → Matrix(s)(C)
Matrix.proj(lift-binOp(_▫_) (v₁)(v₂))(x , y) = Matrix.proj(v₁)(x , y) ▫ Matrix.proj(v₂)(x , y)

-- Matrix from a vector of vectors. The inner vectors becomes rows.
rowMat : ∀{w h}{T} → Vector(h)(Vector(w)(T)) → Matrix(w , h)(T) → Unit{0}
rowMat(vs) _ = <>

-- Matrix from a vector of vectors. The inner vectors becomes columns.
colMat : ∀{w h}{T} → Vector(w)(Vector(h)(T)) → Matrix(w , h)(T) → Unit{0}
colMat(vs) _ = <>

-- Matrix with one row and one column removed
minor : ∀{w h}{T} → Matrix(𝐒(w) , 𝐒(h))(T) → (ℕfin(𝐒(w)) ⨯ ℕfin(𝐒(h))) → Matrix(w , h)(T) → Unit{0}
minor(m)(x , y) _ = <>

-- A square matrix is a matrix with equal length in both directions
SquareMatrix : ℕ → Type → Type
SquareMatrix(d)(T) = Matrix(d , d)(T)

module SquareMatrix {d}{T} where
  module _ (m : SquareMatrix(d)(T)) where
    -- The diagonal vector
    diag : Vector(d)(T)
    Vector.proj(diag)(i) = Matrix.proj(m)(i , i)

    -- The maximum number of dimensions of a space that the matrix can describe linear transformations in
    dim : ℕ
    dim = d

  -- Diagonal matrix from a vector
  diagMat : Vector(d)(T) → SquareMatrix(d)(T) → Unit{0}
  diagMat(v) _ = <>

RowVector : ℕ → Type → Type
RowVector(d)(T) = Matrix(d , 1)(T)

module RowVector {d}{T} where
  rowVecMat : Vector(d)(T) → RowVector(d)(T)
  Matrix.proj(rowVecMat(v))(x , _) = Vector.proj(v)(x)

ColVector : ℕ → Type → Type
ColVector(d)(T) = Matrix(1 , d)(T)

module ColVector {d}{T} where
  colVecMat : Vector(d)(T) → ColVector(d)(T)
  Matrix.proj(colVecMat(v))(_ , y) = Vector.proj(v)(y)
