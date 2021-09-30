module Structure.Operator.Proofs.EquivalentStructure where

import      Data.Tuple as Tuple
open import Functional hiding (id)
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Equiv
import      Lvl
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator
open import Structure.Operator.Group
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  private variable _▫_ : T → T → T

  cancellationₗ-injective : Cancellationₗ(_▫_) ↔ (∀{x} → Injective(x ▫_))
  cancellationₗ-injective = [↔]-intro (\p → intro(Injective.proof p)) (\(intro p) → intro p)

  cancellationᵣ-injective : Cancellationᵣ(_▫_) ↔ (∀{x} → Injective(_▫ x))
  cancellationᵣ-injective = [↔]-intro (\p → intro(Injective.proof p)) (\(intro p) → intro p)

  module _ (_▫_ : T → T → T) where
    group-to-monoid : ⦃ Group(_▫_) ⦄ → Monoid(_▫_)
    group-to-monoid ⦃ intro ⦄ = record{}

    module _ (inv : T → T) where
      monoid-to-group : ⦃ monoid : Monoid(_▫_) ⦄ → ⦃ func : Function(inv) ⦄ → let open Monoid monoid in ⦃ inv : InverseFunction(_▫_)(inv) ⦄ → Group(_▫_)
      Group.identity-existence (monoid-to-group ⦃ intro ⦄) = _
      Group.inverse-existence  (monoid-to-group ⦃ intro ⦄) = [∃]-intro inv

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  private variable _▫_ : T → T → Type{ℓ}

  symmetry-swap-sub : Symmetry(_▫_) ↔ ((_▫_) ⊆₂ swap(_▫_))
  symmetry-swap-sub = [↔]-intro (\(intro p) → intro p) (\(intro p) → intro p)

  symmetry-commutativity : Symmetry(_▫_) ↔ Commutativity ⦃ [↔]-equiv ⦄ (_▫_)
  symmetry-commutativity = [↔]-intro (\(intro p) → intro([↔]-to-[→] p)) (\(intro p) → intro([↔]-intro p p))
