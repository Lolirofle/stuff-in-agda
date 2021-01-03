module Type.Size.Finite where

import      Lvl
open import Functional
open import Logic
open import Logic.Predicate
open import Numeral.Finite
open import Numeral.Finite.Equiv
open import Numeral.Natural
open import Structure.Setoid
open import Type
open import Type.Size

private variable ℓ ℓₑ : Lvl.Level

-- Definition of a finite type
Finite : (T : Type{ℓ}) → ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → Stmt
Finite(T) = ∃(n ↦ 𝕟(n) ≍ T)

#_ : (T : Type{ℓ}) → ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → ⦃ fin : Finite(T) ⦄ → ℕ
#_ _ ⦃ fin = [∃]-intro(n) ⦄ = n

enum : ∀{T : Type{ℓ}} → ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → ⦃ fin : Finite(T) ⦄ → 𝕟(# T) → T
enum ⦃ fin = [∃]-intro _ ⦃ [∃]-intro f ⦄ ⦄ = f

module Finite where
  import      Data.Either as Type
  import      Data.Either.Equiv as Either
  import      Data.Tuple as Type
  import      Data.Tuple.Equiv as Tuple
  open import Numeral.Finite.Sequence
  open import Structure.Function.Domain
  import      Numeral.Natural.Oper as ℕ

  private variable A B : Type{ℓ}
  private variable ⦃ equiv-A ⦄ : Equiv{ℓₑ}(A)
  private variable ⦃ equiv-B ⦄ : Equiv{ℓₑ}(B)
  private variable ⦃ equiv-A‖B ⦄ : Equiv{ℓₑ}(A Type.‖ B)
  private variable ⦃ equiv-A⨯B ⦄ : Equiv{ℓₑ}(A Type.⨯ B)

  _+_ :  ⦃ ext : Either.Extensionality ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ (equiv-A‖B) ⦄ → Finite(A) ⦃ equiv-A ⦄ → Finite(B) ⦃ equiv-B ⦄ → Finite(A Type.‖ B) ⦃ equiv-A‖B ⦄
  _+_ ([∃]-intro a ⦃ [∃]-intro af ⦄) ([∃]-intro b ⦃ [∃]-intro bf ⦄) = [∃]-intro (a ℕ.+ b) ⦃ [∃]-intro (interleave af bf) ⦃ interleave-bijective ⦄ ⦄

  -- TODO: Below
  _⋅_ :  ⦃ ext : Tuple.Extensionality ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ (equiv-A⨯B) ⦄ → Finite(A) ⦃ equiv-A ⦄ → Finite(B) ⦃ equiv-B ⦄ → Finite(A Type.⨯ B) ⦃ equiv-A⨯B ⦄
  _⋅_ ([∃]-intro a ⦃ [∃]-intro af ⦄) ([∃]-intro b ⦃ [∃]-intro bf ⦄) = [∃]-intro (a ℕ.⋅ b) ⦃ [∃]-intro (f af bf) ⦃ p ⦄ ⦄ where
    postulate f : (𝕟(a) → _) → (𝕟(b) → _) → 𝕟(a ℕ.⋅ b) → (_ Type.⨯ _)
    postulate p : Bijective(f af bf)

  {-
  _^_ :  Finite(A) → Finite(B) → Finite(A ← B)
  _^_ ([∃]-intro a ⦃ [∃]-intro af ⦄) ([∃]-intro b ⦃ [∃]-intro bf ⦄) = [∃]-intro (a ℕ.^ b) ⦃ [∃]-intro (f af bf) ⦃ p ⦄ ⦄ where
    postulate f : (𝕟(a) → _) → (𝕟(b) → _) → 𝕟(a ℕ.^ b) → (_ ← _)
    postulate p : Bijective(f af bf)
  -}
