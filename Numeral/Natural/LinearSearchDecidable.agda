module Numeral.Natural.LinearSearchDecidable where

open import Data.Boolean
open import Data.Boolean.Stmt
open import Functional
open import Logic
open import Logic.Computability
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Relation.Order
open import Structure.Relator.Ordering

searchUntilUpperBound : (f : ℕ → Bool) → ∃(IsTrue ∘ f) → ℕ
searchUntilUpperBound f ([∃]-intro upperBound ⦃ proof ⦄) = {!fold!}

searchUntilUpperBoundProof : ∀{f}{upperBound} → (IsTrue ∘ f)(searchUntilUpperBound f upperBound)
searchUntilUpperBoundProof = {!!}

bruteforceMinExistence : ∀{ℓ} → (P : ℕ → Stmt{ℓ}) → ⦃ ComputablyDecidable(P) ⦄ → ∃(P) → ∃(Weak.Properties.MinimumOf(_≤_)(P))
∃.witness (bruteforceMinExistence P upperBound) = {!!}
∃.proof   (bruteforceMinExistence P upperBound) = {!!}
