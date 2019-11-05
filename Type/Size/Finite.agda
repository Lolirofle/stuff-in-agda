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
Finite(T) = ∃(n ↦ T ≍ 𝕟(n))

#_ : (T : Type{ℓ}) → ⦃ _ : Finite(T) ⦄ → ℕ
#_ _ ⦃ [∃]-intro(n) ⦄ = n

{- TODO
enum : ∀{T : Type{ℓ}} → ⦃ fin : Finite(T) ⦄ → 𝕟(#_ T ⦃ fin ⦄) → T
enum ⦃ [∃]-intro _ ⦃ bij ⦄ ⦄ = ?
-}


{-
module Finite where
  private variable ℓ₁ ℓ₂ : Lvl.Level
  private variable A : Type{ℓ₁}
  private variable B : Type{ℓ₂}

  _+_ : Finite(A) → Finite(B) → Finite(A ‖ B)
  _⨯_ : Finite(A) → Finite(B) → Finite(A ⨯ B)
  _^_ : Finite(A) → Finite(B) → Finite(B → A)
-}
