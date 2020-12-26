module Type.Size.Countable where

open import Data.Either
open import Data.Tuple
import      Lvl
open import Functional
open import Logic
open import Logic.Predicate
open import Numeral.Natural
open import Structure.Setoid.WithLvl
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Type
open import Type.Size
open import Type.Size.Proofs

private variable ℓ ℓ₁ ℓ₂ ℓₑ : Lvl.Level

-- Definition of a countable type
Countable : (T : Type{ℓ}) → ⦃ _ : Equiv{ℓₑ}(T) ⦄ → Stmt
Countable(T) = (ℕ ≽ T)

-- Definition of a countably infinite type
CountablyInfinite : (T : Type{ℓ}) → ⦃ _ : Equiv{ℓₑ}(T) ⦄ → Stmt
CountablyInfinite(T) = (ℕ ≍' T) where
  _≍'_ : (A : Type{ℓ₁}) → (B : Type{ℓ₂}) → ⦃ _ : Equiv{ℓₑ}(B) ⦄ → Stmt
  _≍'_ A B ⦃ equiv-B ⦄ = _≍_ A ⦃ [≡]-equiv ⦄ B ⦃ equiv-B ⦄ where
    open import Relator.Equals.Proofs.Equiv

module Countable where
  private variable A : Type{ℓ₁}
  private variable B : Type{ℓ₂}
  private variable ⦃ equiv-A ⦄ : Equiv{ℓₑ}(A)
  private variable ⦃ equiv-B ⦄ : Equiv{ℓₑ}(B)
  private variable ⦃ equiv-A‖B ⦄ : Equiv{ℓₑ}(A ‖ B)
  private variable ⦃ equiv-A⨯B ⦄ : Equiv{ℓₑ}(A ⨯ B)

  -- _+_ : Countable (A) ⦃ equiv-A ⦄ → Countable(B) ⦃ equiv-B ⦄ → Countable(A ‖ B) ⦃ equiv-A‖B ⦄
  -- [∃]-intro a ⦃ intro pa ⦄ + [∃]-intro b ⦃ intro pb ⦄ = [∃]-intro (Left ∘ a) ⦃ intro (\{y} → [∃]-intro ([∃]-witness pa) ⦃ {!!} ⦄) ⦄
  -- [∃]-intro (Left ∘ a) ⦃ intro (\{y} → [∃]-intro ([∃]-witness pa) ⦃ {!!} ⦄) ⦄

  -- _⋅_ : Countable (A) ⦃ equiv-A ⦄ → Countable(B) ⦃ equiv-B ⦄ → Countable(A ⨯ B) ⦃ equiv-A⨯B ⦄

module CountablyInfinite where
  open import Relator.Equals.Proofs.Equivalence

  private variable A : Type{ℓ₁}
  private variable B : Type{ℓ₂}

  index : ∀{ℓ} → (T : Type{ℓ}) → ⦃ equiv-T : Equiv{ℓₑ}(T) ⦄ → ⦃ size : CountablyInfinite(T) ⦄ → (ℕ → T)
  index(_) ⦃ size = size ⦄ = [∃]-witness size

  indexing : ∀{ℓ} → (T : Type{ℓ}) → ⦃ equiv-T : Equiv{ℓₑ}(T) ⦄ → ⦃ size : CountablyInfinite(T) ⦄ → (T → ℕ)
  indexing(T) ⦃ size = size ⦄ = [∃]-witness([≍]-symmetry-raw ⦃ [≡]-equiv ⦄ size ⦃ [≡]-to-function ⦄)

{-
  _+_ : CountablyInfinite(A) → CountablyInfinite(B) → CountablyInfinite(A ‖ B)
  _⨯_ : CountablyInfinite(A) → CountablyInfinite(B) → CountablyInfinite(A ⨯ B)
-}
