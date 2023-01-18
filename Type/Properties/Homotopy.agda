module Type.Properties.Homotopy where

open import Functional
import      Lvl
open import Numeral.Natural
open import Structure.Setoid
open import Type
open import Type.Dependent.Sigma
open import Syntax.Function

private variable ℓ ℓ₁ ℓ₂ ℓₑ : Lvl.Level
private variable T A B : Type{ℓ}
private variable n : ℕ

module _ {ℓ} ⦃ equiv : ∀{T : Type{ℓ}} → Equiv{ℓ}(T) ⦄ where -- TODO: Maybe the requirements can be relaxed to a tower of equivalences?
  module Names where
    HomotopyLevel : ℕ → (A : Type{ℓ}) → Type
    HomotopyLevel(𝟎)      (A) = Σ(A)(x ↦ ∀{y} → (y ≡ x))
    HomotopyLevel(𝐒(𝟎))   (A) = ∀{x y : A} → (x ≡ y)
    HomotopyLevel(𝐒(𝐒(n)))(A) = ∀{x y : A} → HomotopyLevel(𝐒(n))(x ≡ y)

    Truncation = HomotopyLevel ∘ 𝐒 ∘ 𝐒

  record HomotopyLevel(n : ℕ) (A : Type{ℓ}) : Type{ℓ} where
    constructor intro
    field proof : Names.HomotopyLevel(n)(A)

  Truncation = HomotopyLevel ∘ 𝐒 ∘ 𝐒

-- TODO: Where should this be stated?
-- ExcludedMiddle : (A : Type{ℓ}) ⦃ equiv-A : Equiv{ℓₑ}(A) ⦄ → Stmt
-- ExcludedMiddle(A) = MereProposition(A) → (IsUnit(A) ∨ IsEmpty(A))
