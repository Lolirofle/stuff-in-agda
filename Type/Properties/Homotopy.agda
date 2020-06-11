module Type.Properties.Homotopy where

import      Lvl
open import Logic
open import Logic.Propositional
open import Numeral.Natural
open import Structure.Setoid.WithLvl
open import Type
open import Type.Dependent
open import Type.Properties.Empty
open import Type.Properties.Singleton.Proofs
open import Type.Properties.Singleton

private variable ℓ ℓₑ : Lvl.Level
private variable T A B : Type{ℓ}
private variable n : ℕ

module _ ⦃ equiv : ∀{ℓ}{T : Type{ℓ}} → Equiv{ℓ}(T) ⦄ where
  HomotopyLevel : ℕ → (A : Type{ℓ}) → Type
  HomotopyLevel(𝟎)   (A) = IsUnit(A)
  HomotopyLevel(𝐒(n))(A) = ∀{x y : A} → HomotopyLevel(n)(x ≡ y)

  Truncation : ℕ → (A : Type{ℓ}) → Type
  Truncation(n) = HomotopyLevel(𝐒(𝐒(n)))



  -- TODO: Move the proofs below
  HomotopyLevel-successor : ⦃ eq-unit : ∀{ℓ}{A : Type{ℓ}} → ⦃ _ : IsUnit(A) ⦄ → (∀{x y : A} → IsUnit(x ≡ y)) ⦄ → HomotopyLevel(n)(A) → HomotopyLevel(𝐒(n))(A)
  HomotopyLevel-successor {n = 𝟎}   ⦃ eq-unit ⦄ p = eq-unit ⦃ p ⦄
  HomotopyLevel-successor {n = 𝐒 n}             p = HomotopyLevel-successor {n = n} p



-- TODO: Where should this be stated?
-- ExcludedMiddle : (A : Type{ℓ}) ⦃ equiv-A : Equiv{ℓₑ}(A) ⦄ → Stmt
-- ExcludedMiddle(A) = MereProposition(A) → (IsUnit(A) ∨ IsEmpty(A))
