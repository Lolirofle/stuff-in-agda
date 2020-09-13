module Data.List.Iterable where

open import Data
open import Data.List
import      Data.List.Functions as List
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Relator.Equals
open import Structure.Container.Iterable
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

instance
  List-iterable : Iterable(List(T))
  Iterable.Element (List-iterable {T = T}) = T
  Iterable.isEmpty List-iterable = List.isEmpty
  Iterable.current List-iterable ∅       = <>
  Iterable.current List-iterable (x ⊰ l) = x
  Iterable.indexStep List-iterable ∅       = <>
  Iterable.indexStep List-iterable (_ ⊰ _) = <>
  Iterable.step List-iterable ∅       = <>
  Iterable.step List-iterable (x ⊰ l) = l

instance
  List-finite-iterable : Iterable.Finite(List-iterable{T = T})
  ∃.witness List-finite-iterable = List.foldᵣ
  ∃.proof List-finite-iterable {iter = ∅}     = [≡]-intro
  ∃.proof List-finite-iterable {iter = x ⊰ l} = [≡]-intro

instance
  List-empty : Iterable.EmptyConstruction(List-iterable{T = T})(∅)
  List-empty = <>

instance
  List-prepend : Iterable.PrependConstruction(List-iterable{T = T})(_⊰_)
  ∃.witness List-prepend = [≡]-intro
  ∃.proof   List-prepend = [∧]-intro [≡]-intro [≡]-intro
