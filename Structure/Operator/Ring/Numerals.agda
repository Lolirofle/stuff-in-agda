open import Structure.Operator.Ring
open import Structure.Setoid
open import Type

module Structure.Operator.Ring.Numerals
  {ℓF ℓₑF ℓₙ₀}
  {F : Type{ℓF}}
  ⦃ equiv-F : Equiv{ℓₑF}(F) ⦄
  {_+_}{_⋅_}
  ⦃ ring : Ring(_+_)(_⋅_) {ℓₙ₀} ⦄
  where

open import Functional
open import Logic.Propositional
import      Lvl
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
  Field-negative-numeral = InfiniteNegativeNumeral.intro((−_) ∘ from-ℕ)

-- Whether an element of the field is the standard representation of a natural number.
data Natural : F → Type{ℓF Lvl.⊔ ℓₑF} where
  zero  : Natural(𝟎)
  succ  : ∀{x} → Natural(x) → Natural(𝐒(x))
  subst : ∀{x y} → (x ≡ y) → (Natural(x) → Natural(y))

Natural-to-ℕ : ∀{x} → Natural(x) → ℕ
Natural-to-ℕ zero          = ℕ.𝟎
Natural-to-ℕ (succ nat)    = ℕ.𝐒(Natural-to-ℕ nat)
Natural-to-ℕ (subst _ nat) = Natural-to-ℕ nat

-- Whether an element of the field is the standard representation of a whole number.
data Whole : F → Type{ℓF Lvl.⊔ ℓₑF} where
  neg   : ∀{x} → Natural(x) → Whole(− x)
  pos   : ∀{x} → Natural(x) → Whole(x)
  subst : ∀{x y} → (x ≡ y) → (Whole(x) → Whole(y))

Whole-to-ℕ : ∀{x} → Whole(x) → ℤ
Whole-to-ℕ (neg nat)       = ℤ.−ₙ (Natural-to-ℕ nat)
Whole-to-ℕ (pos nat)       = ℤ.+ₙ (Natural-to-ℕ nat)
Whole-to-ℕ (subst _ whole) = Whole-to-ℕ whole

-- Whether an element of the field is the standard representation of a rational number.
data Rational ⦃ div : Division(_+_)(_⋅_) ⦄ : F → Type{ℓF Lvl.⊔ ℓₑF Lvl.⊔ ℓₙ₀} where
  quot  : ∀{a b} → Whole(a) → Natural(b) → ⦃ nonzero-b : NonZero(b) ⦄ → let open Division(div) in Rational(a / b)
  subst : ∀{x y} → (x ≡ y) → (Rational(x) → Rational(y))
