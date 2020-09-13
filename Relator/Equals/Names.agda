module Relator.Equals.Names where

open import Logic
import      Lvl
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Type
open import Type.Size

-- There is a bijection between proofs of equalities and proofs of bijections for types.
Univalence : ∀{ℓ} → Stmt
Univalence{ℓ} = ∀{A B : Type{ℓ}} → (A ≡ B) ≍ (A ≍ B)
