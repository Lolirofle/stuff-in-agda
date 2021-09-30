module Logic.Predicate.Proofs where

import      Lvl
open import Logic.Predicate
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function.Domain
open import Type
open import Type.Properties.MereProposition

module _ {ℓ ℓₗ} {T : Type{ℓ}} {P : T → Type{ℓₗ}} where
  [∃]-witness-injective : ⦃ prop : ∀{x} → MereProposition(P(x)) ⦄ → Injective([∃]-witness {Pred = P})
  Injective.proof [∃]-witness-injective {[∃]-intro x ⦃ px ⦄}{[∃]-intro y ⦃ py ⦄} [≡]-intro
    with [≡]-intro ← uniqueness(P(x)) {px}{py}
    = [≡]-intro
