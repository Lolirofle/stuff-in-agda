module Type.Size.Finite where

import      Lvl
open import Functional
open import Logic
open import Logic.Predicate
open import Numeral.Finite
open import Numeral.Natural
open import Relator.Equals.Proofs.Equivalence
open import Type
open import Type.Size

private variable ℓ : Lvl.Level

-- Definition of a finite type
Finite : Type{ℓ} → Stmt
Finite(T) = ∃(n ↦ 𝕟(n) ≍ T)

#_ : (T : Type{ℓ}) → ⦃ _ : Finite(T) ⦄ → ℕ
#_ _ ⦃ [∃]-intro(n) ⦄ = n

enum : ∀{T : Type{ℓ}} → ⦃ fin : Finite(T) ⦄ → 𝕟(#_ T ⦃ fin ⦄) → T
enum ⦃ fin = [∃]-intro _ ⦃ [∃]-intro f ⦄ ⦄ = f

module Finite where -- TODO: Use Numeral.Finite.Sequence and remove the unused imports
  open import Data.Either as Either using (_‖_)
  open import Data.Either.Proofs
  open import Data.Tuple as Tuple using (_⨯_ ; _,_)
  open import Function.Proofs
  open import Numeral.Finite.Bound
  import      Numeral.Finite.Oper as 𝕟
  open import Numeral.Finite.Proofs
  import      Numeral.Natural.Oper as ℕ
  open import Numeral.Natural.Oper.Proofs
  open import Relator.Equals
  open import Structure.Function.Domain
  open import Structure.Function.Domain.Proofs

  private variable ℓ₁ ℓ₂ : Lvl.Level
  private variable A : Type{ℓ₁}
  private variable B : Type{ℓ₂}

  postulate _+_ : Finite(A) → Finite(B) → Finite(A ‖ B)
  -- _+_ {A = A} {B = B} ([∃]-intro a ⦃ [∃]-intro af ⦄) ([∃]-intro b ⦃ [∃]-intro bf ⦄) = [∃]-intro (a ℕ.+ b) ⦃ {!!} ⦄ where
  postulate _⋅_ : Finite(A) → Finite(B) → Finite(A ⨯ B)
  postulate _^_ : Finite(A) → Finite(B) → Finite(B → A)
