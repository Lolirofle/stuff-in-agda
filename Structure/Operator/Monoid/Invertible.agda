module Structure.Operator.Monoid.Invertible where

open import Functional
import      Lvl
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid
open import Type

private variable ℓ ℓₗ ℓₑ : Lvl.Level
private variable T : Type{ℓ}
private variable _⨞_ : T → T → Type{ℓₗ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) where
  -- Generalizes the following examples in ℕ:
  -- • Lesser than or equal: (5+? = 8)  ⇔ (5 ≤ 8)
  -- • Divides             : (5*? = 10) ⇔ (5 ∣ 10)
  record InverseRelationᵣ(_⨞_ : T → T → Type{ℓₗ}) : Type{Lvl.of(T) Lvl.⊔ ℓₑ Lvl.⊔ ℓₗ} where
    constructor intro
    field proof : ∀{x y} → (x ⨞ y) ↔ ∃(z ↦ x ▫ z ≡ y)

  module _ ⦃ invRel : InverseRelationᵣ{ℓₗ}(_⨞_) ⦄ where
    record InverseOperatorᵣ (_⋄_ : (x : T) → (y : T) → . ⦃ inv : (y ⨞ x) ⦄ → T) : Type{Lvl.of(T) Lvl.⊔ ℓₑ Lvl.⊔ ℓₗ} where
      constructor intro
      field proof : ∀{x y} ⦃ inv : (y ⨞ x) ⦄ → (x ⋄ y ≡ [∃]-witness([↔]-to-[→] (InverseRelationᵣ.proof invRel) inv))

{-
module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) where
  InverseRelationₗ = InverseRelationᵣ(swap(_▫_))

  module _ ⦃ invRel : InverseRelationₗ{ℓₗ}(_⨞_) ⦄ where
    InverseOperatorₗ = InverseOperatorᵣ -- TODO: Is this correct?
-}
