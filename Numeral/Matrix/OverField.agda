open import Structure.Operator.Field
open import Structure.Setoid
open import Type

-- Operators for matrices over a field.
module Numeral.Matrix.OverField {ℓ ℓₑ}{T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {_+ₛ_ _⋅ₛ_ : T → T → T} ⦃ field-structure : Field(_+ₛ_)(_⋅ₛ_) ⦄ where
open Field(field-structure) renaming (_−_ to _−ₛ_ ; −_ to −ₛ_ ; 𝟎 to 𝟎ₛ ; 𝟏 to 𝟏ₛ)

open import Data.Tuple as Tuple using (_,_)
open import Logic.Predicate
open import Numeral.Matrix
open import Numeral.Matrix.Proofs
open import Structure.Operator.Properties

𝟎 : ∀{s} → Matrix(s)(T)
𝟎 = fill(𝟎ₛ)

𝟏 : ∀{n} → Matrix(n , n)(T)
𝟏 = SquareMatrix.scalarMat(𝟎ₛ)(𝟏ₛ)

_+_ : ∀{s} → Matrix(s)(T) → Matrix(s)(T) → Matrix(s)(T)
_+_ = map₂(_+ₛ_)
infixr 1000 _+_

_−_ : ∀{s} → Matrix(s)(T) → Matrix(s)(T) → Matrix(s)(T)
_−_ = map₂(_−ₛ_)
infixr 1000 _−_

−_ : ∀{s} → Matrix(s)(T) → Matrix(s)(T)
−_ = map(−ₛ_)
infixr 1000 −_

_⨯_ : ∀{x y z} → Matrix(y , z)(T) → Matrix(x , y)(T) → Matrix(x , z)(T)
_⨯_ = multPattern(_+ₛ_)(_⋅ₛ_)(𝟎ₛ)
infixr 1000 _⨯_

_⁻¹ : ∀{n} → (M : Matrix(n , n)(T)) ⦃ inver : InvertibleElement(_⨯_) ⦃ [∃]-intro 𝟏 ⦃ {!matrix-multPattern-identity!} ⦄ ⦄ (M) ⦄ → Matrix(n , n)(T)
_⁻¹ _ ⦃ inver ⦄ = [∃]-witness inver
