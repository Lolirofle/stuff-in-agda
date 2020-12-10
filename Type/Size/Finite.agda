module Type.Size.Finite where

import      Lvl
open import Functional
open import Logic
open import Logic.Predicate
open import Numeral.Finite
open import Numeral.Natural
open import Relator.Equals.Proofs.Equiv
open import Type
open import Type.Size

private variable ℓ : Lvl.Level

-- Definition of a finite type
Finite : Type{ℓ} → Stmt
Finite(T) = ∃(n ↦ 𝕟(n) ≍ T)

#_ : (T : Type{ℓ}) → ⦃ _ : Finite(T) ⦄ → ℕ
#_ _ ⦃ [∃]-intro(n) ⦄ = n

enum : ∀{T : Type{ℓ}} → ⦃ fin : Finite(T) ⦄ → 𝕟(# T) → T
enum ⦃ fin = [∃]-intro _ ⦃ [∃]-intro f ⦄ ⦄ = f

module Finite where
  open import Data.Either as Either using (_‖_)
  open import Data.Tuple  as Tuple  using (_⨯_ ; _,_)
  open import Numeral.Finite.Sequence
  open import Structure.Function.Domain
  import      Numeral.Natural.Oper as ℕ

  private variable ℓ₁ ℓ₂ : Lvl.Level
  private variable A : Type{ℓ₁}
  private variable B : Type{ℓ₂}

  _+_ : Finite(A) → Finite(B) → Finite(A ‖ B)
  _+_ ([∃]-intro a ⦃ [∃]-intro af ⦄) ([∃]-intro b ⦃ [∃]-intro bf ⦄) = [∃]-intro (a ℕ.+ b) ⦃ [∃]-intro (interleave af bf) ⦃ interleave-bijective ⦄ ⦄

  -- TODO: Below
  _⋅_ : Finite(A) → Finite(B) → Finite(A ⨯ B)
  _⋅_ ([∃]-intro a ⦃ [∃]-intro af ⦄) ([∃]-intro b ⦃ [∃]-intro bf ⦄) = [∃]-intro (a ℕ.⋅ b) ⦃ [∃]-intro (f af bf) ⦃ p ⦄ ⦄ where
    postulate f : (𝕟(a) → _) → (𝕟(b) → _) → 𝕟(a ℕ.⋅ b) → (_ ⨯ _)
    postulate p : Bijective(f af bf)

  _^_ : Finite(A) → Finite(B) → Finite(A ← B)
  _^_ ([∃]-intro a ⦃ [∃]-intro af ⦄) ([∃]-intro b ⦃ [∃]-intro bf ⦄) = [∃]-intro (a ℕ.^ b) ⦃ [∃]-intro (f af bf) ⦃ p ⦄ ⦄ where
    postulate f : (𝕟(a) → _) → (𝕟(b) → _) → 𝕟(a ℕ.^ b) → (_ ← _)
    postulate p : Bijective(f af bf)
