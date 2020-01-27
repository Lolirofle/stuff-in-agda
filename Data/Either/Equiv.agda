module Data.Either.Equiv where

import      Lvl
open import Data
open import Data.Either as Either
open import Functional
open import Logic.Predicate
open import Structure.Function.Domain hiding (Function)
open import Type

module _ {ℓ} {A B : Type{ℓ}} where
  open import Sets.Setoid
  open import Structure.Relator.Equivalence
  open import Structure.Relator.Properties

  module _ ⦃ equiv-A : Equiv(A) ⦄ ⦃ equiv-B : Equiv(B) ⦄ where
    instance
      Either-equiv : Equiv(A ‖ B)
      Equiv._≡_ Either-equiv (Left  x) (Left  y) = x ≡ y
      Equiv._≡_ Either-equiv (Left  x) (Right y) = Empty
      Equiv._≡_ Either-equiv (Right x) (Left  y) = Empty
      Equiv._≡_ Either-equiv (Right x) (Right y) = x ≡ y
      Reflexivity.proof  (Equivalence.reflexivity  (Equiv.[≡]-equivalence Either-equiv)) {Left  x} = reflexivity(_≡_ {T = A})
      Reflexivity.proof  (Equivalence.reflexivity  (Equiv.[≡]-equivalence Either-equiv)) {Right x} = reflexivity(_≡_ {T = B})
      Symmetry.proof     (Equivalence.symmetry     (Equiv.[≡]-equivalence Either-equiv)) {Left  x} {Left  y} = symmetry(_≡_ {T = A})
      Symmetry.proof     (Equivalence.symmetry     (Equiv.[≡]-equivalence Either-equiv)) {Right x} {Right y} = symmetry(_≡_ {T = B})
      Transitivity.proof (Equivalence.transitivity (Equiv.[≡]-equivalence Either-equiv)) {Left  x} {Left  y} {Left  z} = transitivity(_≡_ {T = A})
      Transitivity.proof (Equivalence.transitivity (Equiv.[≡]-equivalence Either-equiv)) {Right x} {Right y} {Right z} = transitivity(_≡_ {T = B})

    instance
      Left-function : Function ⦃ equiv-A ⦄ ⦃ Either-equiv ⦄ (Left)
      Function.congruence Left-function = id

    instance
      Right-function : Function ⦃ equiv-B ⦄ ⦃ Either-equiv ⦄ (Right)
      Function.congruence Right-function = id
