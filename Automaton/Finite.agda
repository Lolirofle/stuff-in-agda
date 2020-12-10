import      Lvl
open import Structure.Setoid.WithLvl
open import Type

module Automaton.Deterministic.Finite where

open import Data.List renaming (∅ to ε ; _⊰_ to _·_)
open import Data.List.Equiv
open import Data.List.Functions using (postpend ; _++_)
open import Data.List.Proofs
open import Functional
open import Logic
open import Sets.ExtensionalPredicateSet using (PredSet ; intro ; _∈_ ; _∋_ ; ⊶ ; [∋]-binaryRelator)
import      Structure.Function.Names as Names
open import Structure.Operator
open import Structure.Relator.Properties
open import Type.Size.Finite

private variable ℓₚ ℓₛ ℓₑ₁ ℓₐ ℓₑ₂ : Lvl.Level

module _
  {ℓₚ}
  (State : Type{ℓₛ}) ⦃ equiv-state : Equiv{ℓₑ₁}(State) ⦄
  (Alphabet : Type{ℓₐ}) ⦃ equiv-alphabet : Equiv{ℓₑ₂}(Alphabet) ⦄
  where

  record DFA : Type{ℓₛ Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓₑ₂ Lvl.⊔ ℓₐ Lvl.⊔ Lvl.𝐒(ℓₚ)} where
    constructor dfa
    field
      -- ⦃ State-finite ⦄ : Finite(State)
      -- ⦃ Alphabet-finite ⦄ : Finite(Alphabet)
      automata : Deterministic(State)(Alphabet)
