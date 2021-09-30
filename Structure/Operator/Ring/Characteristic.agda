import      Lvl
open import Structure.Operator.Ring
open import Structure.Setoid
open import Type

module Structure.Operator.Ring.Characteristic
  {ℓ ℓₑ}
  {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄
  (_+_ _⋅_  : T → T → T)
  ⦃ rg : Rg(_+_)(_⋅_) ⦄
  where

open Rg(rg)

open import Function.Iteration
open import Numeral.Natural as ℕ using (ℕ)
open import Numeral.Natural.Relation.Divisibility
open import Relator.Equals using () renaming (_≡_ to _≡ₑ_)
open import Structure.Relator.Ordering.Lattice

-- When repeated summation n number of times is zero for all objects in the ring.
-- Example: CharacteristicMultiple(3) ⇔ (a + a + a = 0)
-- If CharacteristicMultiple(n) is satisfied, then n is a multiple of the characteristic of the ring.
CharacteristicMultiple : ℕ → Type
CharacteristicMultiple(n) = ∀{a} → (repeatₗ(n)(_+_) 𝟎 a ≡ 𝟎)

-- The characteristic is the least number of times in a repeated summation equal to zero.
Characteristic : ℕ → Type
Characteristic = LE.Minimum(_∣_)(CharacteristicMultiple)
