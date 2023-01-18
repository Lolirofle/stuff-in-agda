import      Lvl
open import Structure.Set
open import Structure.Setoid
open import Type

module Automaton.Deterministic
  {ℓₐ ℓₑₐ} (Alphabet : Type{ℓₐ}) ⦃ equiv-alphabet : Equiv{ℓₑₐ}(Alphabet) ⦄
  {ℓₛ ℓₑₛ} (State : Type{ℓₛ}) ⦃ equiv-state : Equiv{ℓₑₛ}(State) ⦄
  {ℓₛₛ ℓₑₛₛ ℓₛₛₛ} (StateSet : Type{ℓₛₛ}) ⦃ equiv-state-set : Equiv{ℓₑₛₛ}(StateSet) ⦄
  {_∈_ : State → StateSet → Type{ℓₛₛₛ}} ⦃ state-set-ext : SetExtensionality(_∈_) ⦄
  where

open import Data.List using (List)
open import Structure.Operator

Word = List(Alphabet)
open Data.List renaming (∅ to ε ; _⊰_ to _·_) public

-- Deterministic Automata.
-- `State`      (Q)  is the set of states.
-- `Alphabet`   (Σ)  is the set of symbols/the alphabet.
-- `transition` (δ)  is the transition function.
-- `start`      (q₀) is the start state.
-- `Final`      (F)  is the subset of State which are the final/accepting states.
-- Source: http://www.cse.chalmers.se/edu/course/TMV027/lec5.pdf
record Deterministic : Type{ℓₐ Lvl.⊔ ℓₑₐ Lvl.⊔ ℓₛ Lvl.⊔ ℓₑₛ Lvl.⊔ ℓₛₛ Lvl.⊔ ℓₑₛₛ Lvl.⊔ ℓₛₛₛ} where
  constructor deterministic
  field
    transition : Alphabet → State → State
    ⦃ transition-function ⦄ : BinaryOperator(transition)
    start : State
    final : StateSet

  -- Chained transition using a word.
  wordTransition : State → Word → State
  wordTransition s ε       = s
  wordTransition s (a · l) = wordTransition (transition a s) l

  module LetterNotation where
    Q  = State
    Σ  = Alphabet
    δ  = transition
    δ̂  = wordTransition
    q₀ = start
    F  = final
