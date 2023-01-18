import      Lvl
open import Structure.Set
open import Structure.Setoid
open import Type

module Automaton.NonDeterministic
  {ℓₐ ℓₑₐ} (Alphabet : Type{ℓₐ}) ⦃ equiv-alphabet : Equiv{ℓₑₐ}(Alphabet) ⦄
  {ℓₛ ℓₑₛ} (State : Type{ℓₛ}) ⦃ equiv-state : Equiv{ℓₑₛ}(State) ⦄
  {ℓₛₛ ℓₑₛₛ ℓₛₛₛ} (StateSet : Type{ℓₛₛ}) ⦃ equiv-state-set : Equiv{ℓₑₛₛ}(StateSet) ⦄
  {_∈_ : State → StateSet → Type{ℓₛₛₛ}} ⦃ state-set-ext : SetExtensionality(_∈_) ⦄
  where

open import Data.List using (List)
open import Structure.Operator

Word = List(Alphabet)
open Data.List renaming (∅ to ε ; _⊰_ to _·_) public

-- Non-deterministic Automata
-- `State`      (Q)  is the set of states.
-- `Alphabet`   (Σ)  is the set of symbols/the alphabet.
-- `transition` (δ)  is the transition function.
-- `start`      (q₀) is the start state.
-- `Final`      (F)  is the subset of State which are the final/accepting states.
record NonDeterministic : Type{ℓₐ Lvl.⊔ ℓₑₐ Lvl.⊔ ℓₛ Lvl.⊔ ℓₑₛ Lvl.⊔ ℓₛₛ Lvl.⊔ ℓₑₛₛ Lvl.⊔ ℓₛₛₛ} where
  constructor nondeterministic
  field
    transition : State → Alphabet → StateSet
    ⦃ transition-binaryOperator ⦄ : BinaryOperator(transition)
    start      : State
    final      : StateSet
{-
  -- Chained transition using a word.
  wordTransition : State → Word → PredSet{ℓₛ Lvl.⊔ ℓₜ Lvl.⊔ ℓₑₛ}(State)
  wordTransition s ε       = predLvl(ℓₛ Lvl.⊔ ℓₜ) (• s)
  wordTransition s (a · l) = ⋃ᵢₛ(transition s a) (swap wordTransition l)
-}
  module LetterNotation where
    Q  = State
    Σ  = Alphabet
    δ  = transition
    --δ̂  = wordTransition
    q₀ = start
    F  = final
