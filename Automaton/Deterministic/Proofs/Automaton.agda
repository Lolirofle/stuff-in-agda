import      Lvl
open import Structure.Set
open import Structure.Setoid
open import Type

module Automaton.Deterministic.Proofs.Automaton
  {ℓₐ ℓₑₐ} (Alphabet : Type{ℓₐ}) ⦃ equiv-alphabet : Equiv{ℓₑₐ}(Alphabet) ⦄
  {ℓₛ ℓₑₛ} (State : Type{ℓₛ}) ⦃ equiv-state : Equiv{ℓₑₛ}(State) ⦄
  {ℓₛₛ ℓₑₛₛ ℓₛₛₛ} (StateSet : Type{ℓₛₛ}) ⦃ equiv-state-set : Equiv{ℓₑₛₛ}(StateSet) ⦄
  {_∈_ : State → StateSet → Type{ℓₛₛₛ}} ⦃ state-set-ext : SetExtensionality(_∈_) ⦄
  where

open import Data.List using (List)
open import Structure.Operator

  {-
  open import Automaton
  open import Data
  open import Functional
  open import Data.Boolean
  open import Structure.Function
  open import Type.Identity.Proofs
  automaton : Automaton Alphabet (Unit{Lvl.𝟎}) ⦃ Id-equiv ⦄ Bool ⦃ Id-equiv ⦄
  Automaton.Configuration         automaton = State
  Automaton.initial               automaton = const start
  Automaton.transition            automaton = transition
  Automaton.input                 automaton = const <>
  Automaton.output                automaton = isFinal
  Automaton.initial-function      automaton = {!const-function!}
  Automaton.input-function        automaton = {!const-function!}
  Automaton.initial-input-inverse automaton = {!!}
  -}
