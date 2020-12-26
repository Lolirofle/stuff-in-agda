import      Lvl
open import Structure.Operator.Ring
open import Structure.Setoid
open import Type

module Structure.Operator.Ring.Characteristic {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ (_+_ _⋅_  : T → T → T) ⦃ ring : Ring(_+_)(_⋅_) ⦄ where
open Ring(ring)

open import Function.Iteration
open import Numeral.Natural as ℕ using (ℕ)
import      Numeral.Natural.Relation.Order as ℕ
open import Relator.Equals using () renaming (_≡_ to _≡ₑ_)

CharacteristicMultiple : ℕ → Type
CharacteristicMultiple(n) = ∀{a} → (repeatᵣ(n)(_+_) a 𝟎 ≡ 𝟎)

data Characteristic : ℕ → Type{ℓ Lvl.⊔ ℓₑ} where
  none : (∀{n} → CharacteristicMultiple(n) → (n ≡ₑ ℕ.𝟎)) → Characteristic(ℕ.𝟎)
  pos  : ∀{n} → CharacteristicMultiple(ℕ.𝐒(n)) → (∀{m} → CharacteristicMultiple(ℕ.𝐒(m)) → (ℕ.𝐒(m) ℕ.≥ ℕ.𝐒(n))) → Characteristic(ℕ.𝐒(n))
