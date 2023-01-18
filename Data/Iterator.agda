module Data.Iterator where

import      Lvl
open import Data hiding (empty)
open import Data.Boolean
open import Functional
open import Numeral.Natural
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable a x init : T
private variable f : A → B
private variable n : ℕ

-- TODO: Is this useful when not lazy? It cannot store data and I am not sure if the whole list is evaluated in listIterator or not (strictness)
record Iterator (T : Type{ℓ}) : Type{ℓ} where
  coinductive
  field
    isEmpty : Bool
    current : if isEmpty then Unit else T -- TODO: These are essentially `Option`s but instead of storing its state, they depend on a boolean defined somewhere else
    step    : if isEmpty then Unit else Iterator(T)

open Iterator

{- TODO: This is a generalization of an iterator. It could be used to define iterators for any number of dimensions or to define double-ended iterators.
-- TODO: decidable-all-step may also be ∃{Obj = (Step → Bool) → Bool}(dec ↦ ∀{P} → (IsTrue(dec(P)) ↔ ∀ₗ(IsTrue ∘ P))). Not sure if it captures that (∀{s} → atEnd s) always is decidable by the smallest amount of assumptions. An example of this is when Step is finitely enumerable.
record Stepper (Step : Type{ℓₛ}) ⦃ decidable-all-step : ∀{P : Step → Bool} → Decidable(∀ₗ(IsTrue ∘ P)) ⦄ (T : Type{ℓ}) : Type{ℓ} where
  coinductive
  field
    atEnd : Step → Bool
    current : if decide(∀ₗ(IsTrue ∘ atEnd)) then Unit else T
    step    : (step : Step) → if(atEnd step) then Unit else Stepper(Step)(T)
-}

open import Data.Option
open import Data.Boolean.Operators
open        Data.Boolean.Operators.Programming

skip : ℕ → Iterator(T) → Iterator(T)
skip 𝟎 iter = iter
skip (𝐒 n) iter with isEmpty iter | step iter
... | 𝑇 | <>    = iter
... | 𝐹 | sIter = skip n sIter

skipExact : ℕ → Iterator(T) → Option(Iterator(T))
skipExact 𝟎 iter = Some iter
skipExact (𝐒 n) iter with isEmpty iter | step iter
... | 𝑇 | <>    = None
... | 𝐹 | sIter = skipExact n sIter

{- TODO: Not sure if I did not get the semantics of how codata works or whether the termination checker is wrong
{-# TERMINATING #-}
_++_ : Iterator(T) → Iterator(T) → Iterator(T)
isEmpty (a ++ b) with isEmpty a
... | 𝑇 = isEmpty b
... | 𝐹 = 𝐹
current (a ++ b) with isEmpty a | current a
... | 𝐹 | ca = ca
... | 𝑇 | <> with isEmpty b | current b
...     | 𝐹 | cb = cb
...     | 𝑇 | <> = <>
step (a ++ b) with isEmpty a | step a
... | 𝐹 | sa = sa ++ b
... | 𝑇 | <> with isEmpty b | step b
...     | 𝐹 | sb = sb
...     | 𝑇 | <> = <>

{-# TERMINATING #-}
map : (A → B) → (Iterator(A) → Iterator(B))
isEmpty (map f iter) = isEmpty iter
current (map f iter) with isEmpty iter | current iter
... | 𝑇 | <> = <>
... | 𝐹 | a = f(a)
step    (map f iter) with isEmpty iter | step iter
... | 𝑇 | <>    = <>
... | 𝐹 | sIter = map f sIter
-}

empty : Iterator(T)
isEmpty empty = 𝑇
current empty = <>
step    empty = <>

prepend : T → Iterator(T) → Iterator(T)
isEmpty (prepend x l) = 𝐹
current (prepend x l) = x
step    (prepend x l) = l

open import Data.List as List using (List)

listIterator : List(T) → Iterator(T)
listIterator List.empty         = empty
listIterator (List.prepend x l) = prepend x (listIterator l)
