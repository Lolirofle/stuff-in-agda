module Type.Size.Countable where

open import Data.Either
open import Data.Tuple
import      Lvl
open import Functional
open import Logic
open import Logic.Predicate
open import Numeral.Natural
open import Structure.Setoid
open import Structure.Function.Domain
open import Type
open import Type.Size

-- Definition of a countable type
Countable : ∀{ℓ} → (T : Type{ℓ}) → ⦃ _ : Equiv(T) ⦄ → Stmt
Countable(T) = (ℕ ≽ T)

-- Definition of a countably infinite type
CountablyInfinite : ∀{ℓ} → (T : Type{ℓ}) → ⦃ _ : Equiv(T) ⦄ → Stmt
CountablyInfinite(T) = (ℕ ≍' T) where
  _≍'_ : ∀{ℓ₁ ℓ₂} → (A : Type{ℓ₁}) → (B : Type{ℓ₂}) → ⦃ _ : Equiv(B) ⦄ → Stmt
  _≍'_ A B ⦃ equiv-B ⦄ = _≍_ A ⦃ [≡]-equiv ⦄ B ⦃ equiv-B ⦄ where
    open import Relator.Equals.Proofs.Equivalence

module Countable where
  private variable ℓ₁ ℓ₂ : Lvl.Level
  private variable A : Type{ℓ₁}
  private variable B : Type{ℓ₂}
  private variable ⦃ equiv-A ⦄ : Equiv(A)
  private variable ⦃ equiv-B ⦄ : Equiv(B)
  private variable ⦃ equiv-A‖B ⦄ : Equiv(A ‖ B)
  private variable ⦃ equiv-A⨯B ⦄ : Equiv(A ⨯ B)

  -- _+_ : Countable (A) ⦃ equiv-A ⦄ → Countable(B) ⦃ equiv-B ⦄ → Countable(A ‖ B) ⦃ equiv-A‖B ⦄
  -- [∃]-intro a ⦃ intro pa ⦄ + [∃]-intro b ⦃ intro pb ⦄ = [∃]-intro (Left ∘ a) ⦃ intro (\{y} → [∃]-intro ([∃]-witness pa) ⦃ {!!} ⦄) ⦄
  -- [∃]-intro (Left ∘ a) ⦃ intro (\{y} → [∃]-intro ([∃]-witness pa) ⦃ {!!} ⦄) ⦄

  -- _⋅_ : Countable (A) ⦃ equiv-A ⦄ → Countable(B) ⦃ equiv-B ⦄ → Countable(A ⨯ B) ⦃ equiv-A⨯B ⦄

module CountablyInfinite where
  private variable ℓ₁ ℓ₂ : Lvl.Level
  private variable A : Type{ℓ₁}
  private variable B : Type{ℓ₂}

  indexing : ∀{ℓ} → (T : Type{ℓ}) → ⦃ equiv-T : Equiv(T) ⦄ → ⦃ size : CountablyInfinite(T) ⦄ → (ℕ → T)
  indexing(T) ⦃ size = [∃]-intro f ⦄ = f

{-
  _+_ : CountablyInfinite(A) → CountablyInfinite(B) → CountablyInfinite(A ‖ B)
  _⨯_ : CountablyInfinite(A) → CountablyInfinite(B) → CountablyInfinite(A ⨯ B)
-}
