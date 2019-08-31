-- TODO: Maybe move to Functional?
module Numeral.Matrix {ℓ} where

import      Lvl
open import Syntax.Number
open import Data
open import Data.Boolean
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional using (const)
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Finite.Oper
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Natural
open import Numeral.CoordinateVector as Vector using (Vector)
open import Type{ℓ}

-- Data in 2-dimensional finite space (Implies bounded).
-- Like a data table.
record Matrix (s : ℕ ⨯ ℕ) (T : Type) : Type where
  constructor mat

  -- Type of elements in the matrix
  Element : Type
  Element = T

  -- Width of the matrix (Number of columns)
  width : ℕ
  width = Tuple.left(s)

  -- Height of the matrix (Number of rows)
  height : ℕ
  height = Tuple.right(s)

  field
    -- Projection of a matrix
    -- A cell in the matrix
    proj : (𝕟(width) ⨯ 𝕟(height)) → T

  -- Vector of a row in the matrix
  row : 𝕟(height) → Vector(width)(T)
  Vector.proj(row(y))(x) = proj(x , y)

  -- Vector of a column in the matrix
  col : 𝕟(width) → Vector(height)(T)
  Vector.proj(col(x))(y) = proj(x , y)

  -- Transpose (Reflection on main diagonal)
  ⬔_ : Matrix(height , width)(T)
  proj(⬔_)(x , y) = proj(y , x)

module Rows where
  -- A matrix with two rows swapped.
  swap : ∀{w h}{T} → 𝕟(h) → 𝕟(h) → Matrix(w , h)(T) → Matrix(w , h)(T)
  Matrix.proj(swap(y₁)(y₂)(M))(x , y) =
    if      (y ≡? y₁) then Matrix.proj(M)(x , y₂)
    else if (y ≡? y₂) then Matrix.proj(M)(x , y₁)
    else                   Matrix.proj(M)(x , y)

  -- A matrix where a function has been applied to every row.
  map : ∀{w₁ w₂ h}{A B} → (Vector(w₁)(A) → Vector(w₂)(B)) → Matrix(w₁ , h)(A) → Matrix(w₂ , h)(B)
  Matrix.proj(map f(M))(x , y) = Vector.proj(f(Matrix.row(M)(y)))(x)

  -- A matrix where a function has been applied to every element of the specified row.
  mapSingle : ∀{w h}{T} → 𝕟(h) → (T → T) → Matrix(w , h)(T) → Matrix(w , h)(T)
  Matrix.proj(mapSingle target f(M))(x , y) =
    if      (y ≡? target) then f(Matrix.proj(M)(x , y))
    else                       Matrix.proj(M)(x , y)

  -- A matrix where a function has been applied to the specified row.
  applyOn : ∀{w h}{T} → 𝕟(h) → (Vector(w)(T) → Vector(w)(T)) → Matrix(w , h)(T) → Matrix(w , h)(T)
  Matrix.proj(applyOn target f(M))(x , y) =
    if      (y ≡? target) then Vector.proj(f(Matrix.row(M)(y)))(x)
    else                       Matrix.proj(M)(x , y)

module Cols where
  -- A matrix with two columns swapped.
  swap : ∀{w h}{T} → 𝕟(w) → 𝕟(w) → Matrix(w , h)(T) → Matrix(w , h)(T)
  Matrix.proj(swap(x₁)(x₂)(M))(x , y) =
    if      (x ≡? x₁) then Matrix.proj(M)(x₂ , y)
    else if (x ≡? x₂) then Matrix.proj(M)(x₁ , y)
    else                   Matrix.proj(M)(x , y)

  -- A matrix where a function has been applied to every column.
  map : ∀{w h₁ h₂}{A B} → (Vector(h₁)(A) → Vector(h₂)(B)) → Matrix(w , h₁)(A) → Matrix(w , h₂)(B)
  Matrix.proj(map f(M))(x , y) = Vector.proj(f(Matrix.col(M)(x)))(y)

  -- A matrix where a function has been applied to every element of the specified column.
  mapSingle : ∀{w h}{T} → 𝕟(w) → (T → T) → Matrix(w , h)(T) → Matrix(w , h)(T)
  Matrix.proj(mapSingle target f(M))(x , y) =
    if      (y ≡? target) then f(Matrix.proj(M)(x , y))
    else                       Matrix.proj(M)(x , y)

  -- A matrix where a function has been applied to the specified column.
  applyOn : ∀{w h}{T} → 𝕟(w) → (Vector(h)(T) → Vector(h)(T)) → Matrix(w , h)(T) → Matrix(w , h)(T)
  Matrix.proj(applyOn target f(M))(x , y) =
    if      (x ≡? target) then Vector.proj(f(Matrix.col(M)(x)))(y)
    else                       Matrix.proj(M)(x , y)

-- A matrix where a function has been applied to every element.
map : ∀{s}{A B} → (A → B) → Matrix(s)(A) → Matrix(s)(B) -- TODO: Same implementation in Vector.agda. Generalize. Maybe like in Haskell? With Applicative, Functor and stuff?
Matrix.proj(map f(m))(x , y) = f(Matrix.proj(m)(x , y))

lift-binOp : ∀{A B C}{s} → (A → B → C) → Matrix(s)(A) → Matrix(s)(B) → Matrix(s)(C)
Matrix.proj(lift-binOp(_▫_) (v₁)(v₂))(x , y) = Matrix.proj(v₁)(x , y) ▫ Matrix.proj(v₂)(x , y)

-- Matrix from a vector of vectors. The inner vectors becomes rows.
rowMat : ∀{w h}{T} → Vector(h)(Vector(w)(T)) → Matrix(w , h)(T)
Matrix.proj(rowMat(vs))(x , y) = Vector.proj(Vector.proj(vs)(y))(x)

-- Matrix from a vector of vectors. The inner vectors becomes columns.
colMat : ∀{w h}{T} → Vector(w)(Vector(h)(T)) → Matrix(w , h)(T)
Matrix.proj(colMat(vs))(x , y) = Vector.proj(Vector.proj(vs)(x))(y)

-- Matrix represented as a vector of vectors where the inner vectors are the rows of the matrix.
rows : ∀{w h}{T} → Matrix(w , h)(T) → Vector(h)(Vector(w)(T))
Vector.proj(Vector.proj(rows(M))(y))(x) = Matrix.proj(M)(x , y)

-- Matrix represented as a vector of vectors where the inner vectors are the columns of the matrix.
cols : ∀{w h}{T} → Matrix(w , h)(T) → Vector(w)(Vector(h)(T))
Vector.proj(Vector.proj(cols(M))(x))(y) = Matrix.proj(M)(x , y)

-- Matrix with one row and one column removed
-- minor : ∀{w h}{T} → Matrix(𝐒(w) , 𝐒(h))(T) → (𝕟(𝐒(w)) ⨯ 𝕟(𝐒(h))) → Matrix(w , h)(T)
-- Matrix.proj(minor(M)(X , Y))(x , y) = Matrix.proj(M)(newX , newY) where
--   newX = if (x ≤? X) then x else 𝐏₀(x)
--   newY = if (y ≤? Y) then y else 𝐏₀(y)

-- Matrix filled with a single element
fill : ∀{w h}{T} → T → Matrix(w , h)(T)
Matrix.proj(fill(elem)) = const(elem)

-- submatrix : ∀{w h}{T} → Matrix(w , h)(T) → ((X , Y) : (𝕟(w) ⨯ 𝕟(h))) → ((W , H) : (𝕟(w −₀ X) ⨯ 𝕟(h −₀ Y))) → Matrix(W −₀ X , H −₀ Y)(T)

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
  diagMat : T → Vector(d)(T) → SquareMatrix(d)(T)
  Matrix.proj(diagMat(zero)(v))(x , y) = if (x ≡? y) then Vector.proj(v)(x) else zero

  -- Scalar matrix
  scalarMat : T → T → SquareMatrix(d)(T)
  scalarMat(zero)(elem) = diagMat(zero)(Vector.fill(elem))

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

multPattern : ∀{A B T₁ T₂}{x y z} → (T₁ → T₂ → T₂) → (A → B → T₁) → T₂ → Matrix(z , y)(A) → Matrix(x , z)(B) → Matrix(x , y)(T₂)
Matrix.proj(multPattern (_+_) (_⋅_) (zero) M₁ M₂)(x , y) = Vector.reduceᵣ(_+_) zero (Vector.lift-binOp (_⋅_) (Matrix.row(M₁)(y)) (Matrix.col(M₂)(x)))
