module Data.Option.Iterable where

open import Data
open import Data.Option
import      Data.Option.Functions as Option
open import Functional
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Relator.Equals
open import Structure.Container.Iterable
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

instance
  Option-iterable : Iterable(Option(T))
  Iterable.Element  (Option-iterable {T = T}) = T
  Iterable.isEmpty   Option-iterable = Option.isNone
  Iterable.current   Option-iterable None     = <>
  Iterable.current   Option-iterable (Some x) = x
  Iterable.indexStep Option-iterable None     = <>
  Iterable.indexStep Option-iterable (Some _) = <>
  Iterable.step      Option-iterable None     = <>
  Iterable.step      Option-iterable (Some x) = None

instance
  Option-finite-iterable : Iterable.Finite(Option-iterable{T = T})
  ∃.witness Option-finite-iterable(_▫_) id None     = id
  ∃.witness Option-finite-iterable(_▫_) id (Some x) = x ▫ id
  ∃.proof Option-finite-iterable {iter = None}   = [≡]-intro
  ∃.proof Option-finite-iterable {iter = Some x} = [≡]-intro

instance
  Option-empty : Iterable.EmptyConstruction(Option-iterable{T = T})(None)
  Option-empty = <>
