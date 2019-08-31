import      Structure.Logic.Classical.NaturalDeduction
-- TODO: Seems like Constructive does not work, but why?

module Structure.Logic.Constructive.Syntax.Algebra {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicalLogic : _ ⦄ where
open Structure.Logic.Classical.NaturalDeduction.ClassicalLogic {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} (classicalLogic)

import      Lvl
open import Syntax.Function
open import Type

-- Transitivitity through an operation on proofs
record Transitivable{ℓ}{T : Type{ℓ}}(_▫_ : T → T → Formula) : Type{ℓₘₗ Lvl.⊔ ℓₒ Lvl.⊔ ℓ} where
  field
    _🝖_ : ∀{a b c} → Proof(a ▫ b) → Proof(b ▫ c) → Proof(a ▫ c)
open Transitivable ⦃ ... ⦄ public

Transitivity-to-Transitivable : ∀{_▫_ : Domain → Domain → Formula} → Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(c ↦ (a ▫ b)∧(b ▫ c) ⟶ (a ▫ c))))) → Transitivable(_▫_)
_🝖_ ⦃ Transitivity-to-Transitivable proof ⦄ {a}{b}{c} ab bc =
  ([→].elim
    ([∀].elim ([∀].elim ([∀].elim proof {a}){b}){c})
    ([∧].intro ab bc)
  )

instance
  [⟶]-transitivable : Transitivable(_⟶_)
  _🝖_ ⦃ [⟶]-transitivable ⦄ = [→].transitivity

instance
  [⟷]-transitivable : Transitivable(_⟷_)
  _🝖_ ⦃ [⟷]-transitivable ⦄ = [↔].transitivity
