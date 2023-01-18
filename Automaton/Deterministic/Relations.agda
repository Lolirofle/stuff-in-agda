import      Lvl
open import Structure.Setoid
open import Type

module Automaton.Deterministic.Relations
  {ℓₐ ℓₑₐ} {Alphabet : Type{ℓₐ}} ⦃ equiv-alphabet : Equiv{ℓₑₐ}(Alphabet) ⦄
  where

open import Automaton.Deterministic(Alphabet) ⦃ equiv-alphabet ⦄
open import Automaton.Deterministic.Proofs ⦃ equiv-alphabet ⦄
open import Data.List.Equiv
open import Sets.ExtensionalPredicateSet using (PredSet ; intro ; _∈_ ; _∋_ ; ⊶ ; [∋]-binaryRelator ; unmap)
open import Structure.Operator

private variable ℓₛ ℓₑₛ ℓₚ ℓₑₗ : Lvl.Level

module _ {State : Type{ℓₛ}} ⦃ equiv-state : Equiv{ℓₑₛ}(State) ⦄ where
  module _ (d : Deterministic(State){ℓₚ}) where
    open Deterministic d

    module _ ⦃ equiv-Word : Equiv{ℓₑₗ}(Word) ⦄ ⦃ ext-Word : Extensionality(equiv-Word) ⦄ where
      -- A word is accepted by the automaton when it can transition from the start state to a final state.
      AcceptsWord : PredSet(Word)
      AcceptsWord = unmap(wordTransition start) ⦃ BinaryOperator-unary₂ wordTransition ⦃ wordTransition-function ⦄ ⦄ Final
