module Automaton.Deterministic where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.List renaming (∅ to ε ; _⊰_ to _·_)
open import Functional
open import Logic
open import Sets.ExtensionalPredicateSet
open import Structure.Setoid.WithLvl
open import Type

-- According to http://www.cse.chalmers.se/edu/course/TMV027/lec5.pdf

-- Deterministic Automata
-- `State`      (Q)  is the set of states.
-- `Alphabet`   (Σ)  is the set of symbols/the alphabet.
-- `transition` (δ)  is the transition function.
-- `start`      (q₀) is the start state.
-- `Final`      (F)  is the subset of State which are the final/accepting states.
record Deterministic {ℓₚ ℓₛ ℓₑ ℓₐ} (State : Type{ℓₛ}) ⦃ equiv-state : Equiv{ℓₑ}(State) ⦄ (Alphabet : Type{ℓₐ}) : Type{ℓₛ ⊔ ℓₑ ⊔ ℓₐ ⊔ Lvl.𝐒(ℓₚ)} where
  constructor deterministic
  field
    transition : State → Alphabet → State
    start      : State
    Final      : PredSet{ℓₚ}(State)

  Word = List(Alphabet)

  -- Chained transition using a word (list of characters).
  transitionWord : State → Word → State
  transitionWord initialState ε       = initialState
  transitionWord initialState (a · l) = transitionWord (transition initialState a) l

  module LetterNotation where
    Q  = State
    Σ  = Alphabet
    δ  = transition
    δ̂  = transitionWord
    q₀ = start
    F  = Final

  -- A word is accepted by the automaton when it can transition from the start state to a final state.
  AcceptsWord : Word → Stmt
  AcceptsWord = (_∈ Final) ∘ transitionWord start

  -- The subset of State which are the accessible states from the start state by chained transitions.
  Accessible : PredSet(State)
  Accessible = ⊶(transitionWord start)

  automatonTransition : Alphabet → Deterministic(State)(Alphabet)
  transition (automatonTransition _) = transition
  start      (automatonTransition c) = transition start c
  Final      (automatonTransition _) = Final

  automatonTransitionWord : Word → Deterministic(State)(Alphabet)
  transition (automatonTransitionWord _) = transition
  start      (automatonTransitionWord w) = transitionWord start w
  Final      (automatonTransitionWord _) = Final
