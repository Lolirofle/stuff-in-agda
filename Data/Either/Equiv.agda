module Data.Either.Equiv where

import      Lvl
open import Data
open import Data.Either as Either
open import Functional
open import Logic
open import Logic.Predicate
open import Structure.Function.Domain
open import Structure.Function
open import Type

module _ {ℓ₁ ℓ₂} {A : Type{ℓ₁}} {B : Type{ℓ₂}} where
  open import Structure.Setoid
  open import Structure.Relator.Equivalence
  open import Structure.Relator.Properties

  module _ ⦃ equiv-A : Equiv(A) ⦄ ⦃ equiv-B : Equiv(B) ⦄ where
    data EitherEquality : (A ‖ B) → (A ‖ B) → Stmt{ℓ₁ ⊔ ℓ₂} where
      Left  : ∀{x y} → (x ≡ y) → EitherEquality(Left  x)(Left  y)
      Right : ∀{x y} → (x ≡ y) → EitherEquality(Right x)(Right y)

    instance
      Either-equiv : Equiv(A ‖ B)
      Equiv._≡_ Either-equiv = EitherEquality
      Reflexivity.proof (Equivalence.reflexivity (Equiv.[≡]-equivalence Either-equiv)) {Left  _} = Left (reflexivity(_≡_))
      Reflexivity.proof (Equivalence.reflexivity (Equiv.[≡]-equivalence Either-equiv)) {Right _} = Right (reflexivity(_≡_))
      Symmetry.proof (Equivalence.symmetry (Equiv.[≡]-equivalence Either-equiv)) {.(Left _)} {.(Left _)} (Left p) = Left (symmetry(_≡_) p)
      Symmetry.proof (Equivalence.symmetry (Equiv.[≡]-equivalence Either-equiv)) {.(Right _)} {.(Right _)} (Right p) = Right (symmetry(_≡_) p)
      Transitivity.proof (Equivalence.transitivity (Equiv.[≡]-equivalence Either-equiv)) {.(Left _)} {.(Left _)} {.(Left _)} (Left xy) (Left yz) = Left (transitivity(_≡_) xy yz)
      Transitivity.proof (Equivalence.transitivity (Equiv.[≡]-equivalence Either-equiv)) {.(Right _)} {.(Right _)} {.(Right _)} (Right xy) (Right yz) = Right (transitivity(_≡_) xy yz)

    instance
      Left-function : Function ⦃ equiv-A ⦄ ⦃ Either-equiv ⦄ (Left)
      Function.congruence Left-function = Left

    instance
      Right-function : Function ⦃ equiv-B ⦄ ⦃ Either-equiv ⦄ (Right)
      Function.congruence Right-function = Right
