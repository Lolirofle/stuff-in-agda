module Lvl.Proofs where

open import Lvl
open import Lvl.Order
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Operator.Lattice
open import Structure.Operator.Properties
open import Structure.Relator.Ordering
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

instance
  [⊔]-commutativity : Commutativity(_⊔_)
  Commutativity.proof [⊔]-commutativity = [≡]-intro

instance
  [⊔]-associativity : Associativity(_⊔_)
  Associativity.proof [⊔]-associativity = [≡]-intro

instance
  [⊔]-idempotent : Idempotence(_⊔_)
  Idempotence.proof [⊔]-idempotent = [≡]-intro

instance
  [⊔]-semiLattice : Semilattice(Level)(_⊔_)
  [⊔]-semiLattice = intro

instance
  [≤]-partialOrder : Weak.PartialOrder(_≤_)
  [≤]-partialOrder = Semilattice.partialOrder [⊔]-semiLattice
