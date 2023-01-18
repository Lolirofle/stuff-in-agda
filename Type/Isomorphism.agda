module Type.Isomorphism where

open import Logic.Predicate
import      Lvl
open import Structure.Function.Domain
open import Structure.Setoid
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level

-- Invertible functions existence between two types.
-- The standard definition of type isomorphism.
-- Two types are isomorphic/equivalent when there is an invertible bidirectional function between them.
-- When viewing types as sets, this means that the cardinality on them are equal.
-- Note: This and Type.Size._≍_ are equivalent. The difference is only in the representation of the fact. This definition is more practical in some cases.
_≍_ : (A : Type{ℓ₁}) → (B : Type{ℓ₂}) → ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ → Type
A ≍ B = ∃(InversePair{A = A}{B = B})
