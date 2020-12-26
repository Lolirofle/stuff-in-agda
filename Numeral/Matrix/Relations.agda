module Numeral.Matrix.Relations where

open import Data.Tuple as Tuple using (_,_)
open import Logic.Predicate
open import Logic
open import Numeral.Matrix hiding (module SquareMatrix)
open import Numeral.Matrix.OverField
import      Relator.Equals as Eq
open import Structure.Operator.Field
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Setoid
open import Syntax.Function
open import Type

module SquareMatrix {ℓ ℓₑ} {d} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  record Symmetric(M : SquareMatrix(d)(T)) : Stmt{ℓₑ} where
    constructor intro
    field proof : ∀{x y} → Matrix.proj M(x , y) ≡ Matrix.proj M(y , x)

  module _ {_▫_ : T → T → T} ⦃ monoid : Monoid(_▫_) ⦄ where
    record Diagonal(M : SquareMatrix(d)(T)) : Stmt{ℓₑ} where
      constructor intro
      field proof : ∀{x y} → (x Eq.≢ y) → (Matrix.proj M(x , y) ≡ Monoid.id monoid)

    record Scalar (s : T) (M : SquareMatrix(d)(T)) : Stmt{ℓₑ} where
      constructor intro
      field
        ⦃ diagonal ⦄ : Diagonal(M)
        proof : ∀{x} → (Matrix.proj M(x , x) ≡ s)

  module _ {_+ₛ_ _⋅ₛ_ : T → T → T} ⦃ field-structure : Field(_+ₛ_)(_⋅ₛ_) ⦄ where  
    record Similar(A B : SquareMatrix(d)(T)) : Stmt{ℓₑ} where
      constructor intro
      field proof : ∃(P ↦ ∃{Obj = Invertible(P)}(inver ↦ B ≡ inv(P) ⨯ A ⨯ P))

    record Diagonalizable(M : SquareMatrix(d)(T)) : Stmt{ℓₑ} where
      constructor intro
      field proof : ∃(P ↦ ∃{Obj = Invertible(P)}(inver ↦ Diagonal(inv(P) ⨯ M ⨯ P)))
