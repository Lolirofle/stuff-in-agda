module Type.Equiv where

open import Function.Proofs
open import Logic.Predicate
import      Lvl
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Setoid
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂ : Lvl.Level

-- Invertible function existence.
-- The standard equivalence/isomorphism for types.
_≍_ : (A : Type{ℓ₁}) → (B : Type{ℓ₂}) → ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ → Type
A ≍ B = ∃(InversePair{A = A}{B = B})

open import Logic.Propositional.Theorems using ([↔]-reflexivity ; [↔]-symmetry ; [↔]-transitivity)
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties

module _ {ℓ ℓₑ} ⦃ equiv : ∀{T : Type{ℓ}} → Equiv{ℓₑ}(T) ⦄ where
  [≍]-reflexivity : Reflexivity{T = Type{ℓ}}(\A B → (A ≍ B))
  Reflexivity.proof [≍]-reflexivity = [∃]-intro _ ⦃ id-inversePair ⦄

  [≍]-symmetry : Symmetry{T = Type{ℓ}}(\A B → (A ≍ B))
  Symmetry.proof [≍]-symmetry _ = [∃]-intro _ ⦃ sym-inversePair ⦄

  module _ ⦃ func : ∀{A B : Type{ℓ}}{f : A → B} → Function(f) ⦄ where
    [≍]-transitivity : Transitivity{T = Type{ℓ}}(\A B → (A ≍ B))
    Transitivity.proof [≍]-transitivity ([∃]-intro xy ⦃ p ⦄) ([∃]-intro yz ⦃ q ⦄) = [∃]-intro _ ⦃ trans-inversePair ⦃ inv₁ = p ⦄ ⦃ inv₂ = q ⦄ ⦄

    [≍]-equivalence : Equivalence{T = Type{ℓ}}(\A B → (A ≍ B))
    [≍]-equivalence = intro ⦃ [≍]-reflexivity ⦄ ⦃ [≍]-symmetry ⦄ ⦃ [≍]-transitivity ⦄
