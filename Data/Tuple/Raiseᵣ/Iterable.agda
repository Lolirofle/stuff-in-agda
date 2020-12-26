module Data.Tuple.Raiseᵣ.Iterable where

open import Data
open import Data.Boolean
open import Data.Tuple
open import Data.Tuple.Raiseᵣ
import      Data.Tuple.Raiseᵣ.Functions as Raiseᵣ
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Numeral.Natural
open import Relator.Equals
open import Structure.Container.IndexedIterable
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

instance
  Raiseᵣ-iterable : Iterable(T ^_)
  Iterable.Element   (Raiseᵣ-iterable {T = T}) = T
  Iterable.isEmpty   Raiseᵣ-iterable {𝟎}    _ = 𝑇
  Iterable.isEmpty   Raiseᵣ-iterable {𝐒(n)} _ = 𝐹
  Iterable.indexStep Raiseᵣ-iterable {𝟎}    _ = <>
  Iterable.indexStep Raiseᵣ-iterable {𝐒(n)} _ = n
  Iterable.current   Raiseᵣ-iterable {𝟎}       <>      = <>
  Iterable.current   Raiseᵣ-iterable {𝐒(𝟎)}    x       = x
  Iterable.current   Raiseᵣ-iterable {𝐒(𝐒(n))} (x , l) = x
  Iterable.step      Raiseᵣ-iterable {𝟎}       <>      = <>
  Iterable.step      Raiseᵣ-iterable {𝐒(𝟎)}    x       = <>
  Iterable.step      Raiseᵣ-iterable {𝐒(𝐒(n))} (x , l) = l

instance
  Raiseᵣ-finite-iterable : Iterable.Finite(Raiseᵣ-iterable{T = T})
  ∃.witness Raiseᵣ-finite-iterable = Raiseᵣ.foldᵣ
  ∃.proof Raiseᵣ-finite-iterable {𝟎}       = [≡]-intro
  ∃.proof Raiseᵣ-finite-iterable {𝐒(𝟎)}    = [≡]-intro
  ∃.proof Raiseᵣ-finite-iterable {𝐒(𝐒(n))} = [≡]-intro

instance
  Raiseᵣ-empty : Iterable.EmptyConstruction(Raiseᵣ-iterable{ℓ}{T = T})(<>)
  Raiseᵣ-empty = <>

instance
  Raiseᵣ-prepend : Iterable.PrependConstruction(Raiseᵣ-iterable{ℓ}{T = T})(Raiseᵣ._⊰_)
  ∃.witness Raiseᵣ-prepend = [≡]-intro
  ∃.proof (Raiseᵣ-prepend {i = 𝟎}     {iter = <>}) = [∧]-intro [≡]-intro [≡]-intro
  ∃.proof (Raiseᵣ-prepend {i = 𝐒(_)})              = [∧]-intro [≡]-intro [≡]-intro
