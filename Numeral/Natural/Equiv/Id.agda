module Numeral.Natural.Equiv.Id where

open import Numeral.Natural
open import Structure.Function
open import Structure.Relator.Equivalence
open import Structure.Setoid
open import Type
open import Type.Identity
open import Type.Identity.Proofs

instance
  ℕ-equiv : Equiv(ℕ)
  ℕ-equiv = Id-equiv

open Equiv(ℕ-equiv) public
  using ()
  renaming (
    equivalence  to ℕ-equivalence  ;
    reflexivity  to ℕ-reflexivity  ;
    symmetry     to ℕ-symmetry     ;
    transitivity to ℕ-transitivity
  )

instance
  ℕ-to-function : ∀{ℓ ℓₑ}{T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {f : ℕ → T} → Function(f)
  ℕ-to-function = Id-to-function
