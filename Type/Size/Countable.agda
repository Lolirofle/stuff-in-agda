module Type.Size.Countable where

import      Data.Either as Type
import      Data.Either.Equiv as Either
import      Data.Tuple as Type
import      Data.Tuple.Equiv as Tuple
import      Lvl
open import Logic
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Sequence
open import Numeral.Natural.Sequence.Proofs
open import Relator.Equals.Proofs.Equivalence
open import Structure.Setoid
open import Type
open import Type.Size
open import Type.Size.Proofs

private variable ℓ ℓ₁ ℓ₂ ℓₑ : Lvl.Level

-- Definition of a countable type
Countable : (T : Type{ℓ}) → ⦃ _ : Equiv{ℓₑ}(T) ⦄ → Stmt
Countable(T) = (ℕ ≽ T)

-- Definition of a countably infinite type
CountablyInfinite : (T : Type{ℓ}) → ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → Stmt
CountablyInfinite(T) ⦃ equiv ⦄ = _≍_ ℕ ⦃ [≡]-equiv ⦄ T

private variable A : Type{ℓ₁}
private variable B : Type{ℓ₂}
private variable ⦃ equiv-A ⦄ : Equiv{ℓₑ}(A)
private variable ⦃ equiv-B ⦄ : Equiv{ℓₑ}(B)
private variable ⦃ equiv-A‖B ⦄ : Equiv{ℓₑ}(A Type.‖ B)
private variable ⦃ equiv-A⨯B ⦄ : Equiv{ℓₑ}(A Type.⨯ B)

module Countable where
  -- TODO: Do something similar to CountablyInfinite here

  -- _+_ : Countable (A) ⦃ equiv-A ⦄ → Countable(B) ⦃ equiv-B ⦄ → Countable(A ‖ B) ⦃ equiv-A‖B ⦄
  -- [∃]-intro a ⦃ intro pa ⦄ + [∃]-intro b ⦃ intro pb ⦄ = [∃]-intro (Left ∘ a) ⦃ intro (\{y} → [∃]-intro ([∃]-witness pa) ⦃ {!!} ⦄) ⦄
  -- [∃]-intro (Left ∘ a) ⦃ intro (\{y} → [∃]-intro ([∃]-witness pa) ⦃ {!!} ⦄) ⦄

  -- _⋅_ : Countable (A) ⦃ equiv-A ⦄ → Countable(B) ⦃ equiv-B ⦄ → Countable(A ⨯ B) ⦃ equiv-A⨯B ⦄

module CountablyInfinite where
  index : ∀{ℓ} → (T : Type{ℓ}) → ⦃ equiv-T : Equiv{ℓₑ}(T) ⦄ → ⦃ size : CountablyInfinite(T) ⦄ → (ℕ → T)
  index(_) ⦃ size = size ⦄ = [∃]-witness size

  indexing : ∀{ℓ} → (T : Type{ℓ}) → ⦃ equiv-T : Equiv{ℓₑ}(T) ⦄ → ⦃ size : CountablyInfinite(T) ⦄ → (T → ℕ)
  indexing(T) ⦃ size = size ⦄ = [∃]-witness([≍]-symmetry-raw ⦃ [≡]-equiv ⦄ size ⦃ [≡]-to-function ⦄)

  _+_ : ⦃ ext : Either.Extensionality ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ (equiv-A‖B) ⦄ → CountablyInfinite(A) ⦃ equiv-A ⦄ → CountablyInfinite(B) ⦃ equiv-B ⦄ → CountablyInfinite(A Type.‖ B) ⦃ equiv-A‖B ⦄
  [∃]-intro a + [∃]-intro b = [∃]-intro (interleave a b)

  _⨯_ : ⦃ ext : Tuple.Extensionality ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ (equiv-A⨯B) ⦄ → CountablyInfinite(A) ⦃ equiv-A ⦄ → CountablyInfinite(B) ⦃ equiv-B ⦄ → CountablyInfinite(A Type.⨯ B) ⦃ equiv-A⨯B ⦄
  [∃]-intro a ⨯ [∃]-intro b = [∃]-intro (pair a b)
