import      Lvl
open import Structure.Operator.Ring
open import Structure.Setoid
open import Type

module Structure.Operator.Ring.Characteristic.Proofs
  {ℓ ℓₑ}
  {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄
  (_+_ _⋅_  : T → T → T)
  where

import      Data.Tuple as Tuple
open import Function.Iteration
open import Function.Iteration.Proofs
open import Logic.Propositional
open import Numeral.Natural as ℕ using (ℕ)
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Relator.Equals using () renaming (_≡_ to _≡ₑ_ ; [≡]-intro to intro)
open import Sets.PredicateSet using () renaming (_≡_ to _≡ₛ_)
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Operator.Ring.Characteristic(_+_)(_⋅_)
open import Structure.Relator
open import Structure.Relator.Ordering.Lattice
open import Structure.Relator.Ordering.Lattice.Proofs
open import Structure.Relator.Properties
open import Syntax.Transitivity

module _ ⦃ rg : Rg(_+_)(_⋅_) ⦄ where
  open Rg(rg)

  open import Relator.Equals.Proofs.Equiv

  -- A ring have a characteristic of 0 when 0 only occurs at the start for iterated applications of addition.
  characteristic-zero : Characteristic(ℕ.𝟎) ↔ (∀{n} → CharacteristicMultiple(n) → (n ≡ₑ ℕ.𝟎))
  Tuple.left  characteristic-zero p = intro ⦃ \{_} → reflexivity(_≡_) ⦄ ⦃ intro(\{x} ⦃ char ⦄ → substitute₂ᵣ(_∣_) (symmetry(_≡ₑ_) (p{x} (\{x} → char{x}))) Div𝟎) ⦄
  Tuple.right characteristic-zero (intro ⦃ correctness ⦄ ⦃ intro minimality ⦄) {n} char = [0]-only-divides-[0] (minimality{n} ⦃ char ⦄)

module _ ⦃ rig : Rig(_+_)(_⋅_) ⦄ where
  open Rig(rig)

  -- In the presense of a multiplicative identity, the definition of a characteristic can be replaced by iterating 1's instead of arbitrary elements.
  characteristic-multiple-by-unity : CharacteristicMultiple ≡ₛ (\n → (repeatₗ(n)(_+_) 𝟎 𝟏 ≡ 𝟎))
  Tuple.left (characteristic-multiple-by-unity {n}) p {a} =
    repeatₗ n (_+_) 𝟎 a       🝖[ _≡_ ]-[ repeatₗ-function (intro{x = n}) (reflexivity(_≡_)) (reflexivity(_≡_) {𝟎}) (identityᵣ(_⋅_)(𝟏)) ]-sym
    repeatₗ n (_+_) 𝟎 (a ⋅ 𝟏) 🝖[ _≡_ ]-[ repeatₗ-distributivityₗ{x = a}{y = 𝟏}{n = n} ]-sym
    a ⋅ (repeatₗ n (_+_) 𝟎 𝟏) 🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_)(a) p ]
    a ⋅ 𝟎                     🝖[ _≡_ ]-[ absorberᵣ(_⋅_)(𝟎) ]
    𝟎                         🝖-end
  Tuple.right characteristic-multiple-by-unity p = p{𝟏}

  -- Similar to `characteristic-multiple-by-unity`.
  characteristic-by-unity : Characteristic ≡ₛ LE.Minimum(_∣_)(\n → repeatₗ(n)(_+_) 𝟎 𝟏 ≡ 𝟎)
  characteristic-by-unity = top-relation(\{n} → characteristic-multiple-by-unity{n})
