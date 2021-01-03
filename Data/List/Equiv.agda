module Data.List.Equiv where

open import Logic.Propositional
import      Lvl
open import Data.List
open import Structure.Operator
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ ℓₚ : Lvl.Level
private variable T : Type{ℓ}

-- A correct equality relation on lists should state that prepend is a function and have the generalized cancellation properties for lists.
record Extensionality ⦃ equiv : Equiv{ℓₑ}(T) ⦄ (equiv-List : Equiv{ℓₚ}(List(T))) : Type{ℓₑ Lvl.⊔ Lvl.of(T) Lvl.⊔ ℓₚ} where
  constructor intro
  private instance _ = equiv-List
  field
    ⦃ binaryOperator ⦄ : BinaryOperator(List._⊰_)
    generalized-cancellationᵣ : ∀{x y : T}{l₁ l₂ : List(T)} → (x ⊰ l₁ ≡ y ⊰ l₂) → (x ≡ y)
    generalized-cancellationₗ : ∀{x y : T}{l₁ l₂ : List(T)} → (x ⊰ l₁ ≡ y ⊰ l₂) → (l₁ ≡ l₂)
    case-unequality : ∀{x : T}{l : List(T)} → (∅ ≢ x ⊰ l)

  generalized-cancellation : ∀{x y : T}{l₁ l₂ : List(T)} → (x ⊰ l₁ ≡ y ⊰ l₂) → ((x ≡ y) ∧ (l₁ ≡ l₂))
  generalized-cancellation p = [∧]-intro (generalized-cancellationᵣ p) (generalized-cancellationₗ p)
open Extensionality ⦃ … ⦄ renaming
  ( binaryOperator to [⊰]-binaryOperator
  ; generalized-cancellationₗ to [⊰]-generalized-cancellationₗ
  ; generalized-cancellationᵣ to [⊰]-generalized-cancellationᵣ
  ; generalized-cancellation to [⊰]-generalized-cancellation
  ; case-unequality to [∅][⊰]-unequal
  ) public
