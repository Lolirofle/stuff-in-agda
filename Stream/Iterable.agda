{-# OPTIONS --guardedness #-}

module Stream.Iterable where

open import Data
open import Data.Boolean
open import Functional
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Relator.Equals
open import Stream as Stream
open import Structure.Container.Iterable
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

instance
  Stream-iterable : Iterable(Stream(T))
  Iterable.Element  (Stream-iterable {T = T}) = T
  Iterable.isEmpty   Stream-iterable = const 𝐹
  Iterable.current   Stream-iterable = Stream.head
  Iterable.indexStep Stream-iterable = const <>
  Iterable.step      Stream-iterable = Stream.tail

instance
  Stream-prepend : Iterable.PrependConstruction(Stream-iterable{T = T})(_⊰_)
  ∃.witness Stream-prepend = [≡]-intro
  ∃.proof (Stream-prepend) = [∧]-intro [≡]-intro [≡]-intro
