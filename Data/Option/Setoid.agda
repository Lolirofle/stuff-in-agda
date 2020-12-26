module Data.Option.Setoid where

import      Lvl
open import Data
open import Data.Option
open import Functional
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid.WithLvl
open import Type

private variable ℓ ℓₑ ℓₑₐ : Lvl.Level
private variable A : Type{ℓ}

instance
  Option-equiv : ⦃ equiv : Equiv{ℓₑ}(A) ⦄ → Equiv{ℓₑ}(Option A)
  Equiv._≡_ Option-equiv None     None     = Unit
  Equiv._≡_ Option-equiv None     (Some _) = Empty
  Equiv._≡_ Option-equiv (Some _) None     = Empty
  Equiv._≡_ Option-equiv (Some x) (Some y) = x ≡ y
  Reflexivity.proof  (Equivalence.reflexivity  (Equiv.equivalence Option-equiv)) {None}   = <>
  Reflexivity.proof  (Equivalence.reflexivity  (Equiv.equivalence Option-equiv)) {Some _} = reflexivity(_≡_)
  Symmetry.proof     (Equivalence.symmetry     (Equiv.equivalence Option-equiv)) {None}   {None}   = const(<>)
  Symmetry.proof     (Equivalence.symmetry     (Equiv.equivalence Option-equiv)) {Some _} {Some _} = symmetry(_≡_)
  Transitivity.proof (Equivalence.transitivity (Equiv.equivalence Option-equiv)) {None}   {None}   {None}   = const(const(<>))
  Transitivity.proof (Equivalence.transitivity (Equiv.equivalence Option-equiv)) {Some _} {Some _} {Some _} = transitivity(_≡_)
