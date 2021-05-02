open import Structure.Operator.Ring
open import Structure.Setoid
open import Type

module Structure.Operator.Ring.Numerals
  {ℓF ℓₑF}
  {F : Type{ℓF}}
  ⦃ equiv-F : Equiv{ℓₑF}(F) ⦄
  {_+_}{_⋅_}
  ⦃ ring : Ring(_+_)(_⋅_) ⦄
  where

open import Functional
open import Numeral.Integer as ℤ using (ℤ)
open import Numeral.Natural as ℕ using (ℕ)
open import Syntax.Number
open import Syntax.Transitivity

module _ where

open Ring(ring)

-- Successor function for fields.
𝐒 : F → F
𝐒 = _+ 𝟏

-- Predecessor function for fields.
𝐏 : F → F
𝐏 = _− 𝟏

-- A standard representation of ℕ in a semi rg.
from-ℕ : ℕ → F
from-ℕ ℕ.𝟎          = 𝟎
from-ℕ ℕ.𝟏          = 𝟏
from-ℕ (ℕ.𝐒(ℕ.𝐒 n)) = 𝐒(from-ℕ (ℕ.𝐒(n)))

-- A standard representation of ℤ in a field.
from-ℤ : ℤ → F
from-ℤ (ℤ.+ₙ x)  = from-ℕ x
from-ℤ (ℤ.−𝐒ₙ x) = − from-ℕ (ℕ.𝐒(x))

instance
  Field-numeral : InfiniteNumeral(F)
  Field-numeral = InfiniteNumeral.intro from-ℕ

instance
  Field-negative-numeral : InfiniteNegativeNumeral(F)
  Field-negative-numeral = InfiniteNegativeNumeral.intro ((−_) ∘ from-ℕ)
