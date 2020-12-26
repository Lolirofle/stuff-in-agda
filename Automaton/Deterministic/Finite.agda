import      Lvl
open import Structure.Setoid.WithLvl
open import Type

module Automaton.Deterministic.Finite where

open import Automaton.Deterministic
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.List renaming (∅ to ε ; _⊰_ to _·_)
open import Data.List.Setoid
open import Data.List.Functions using (postpend ; _++_)
open import Data.List.Proofs
open import Functional
open import Logic.Propositional
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
    field
      ⦃ State-finite ⦄ : Finite(State)
      ⦃ Alphabet-finite ⦄ : Finite(Alphabet)
      automata : Deterministic{ℓₚ = ℓₚ}(State)(Alphabet)
    open Deterministic(automata) hiding (transitionedAutomaton ; wordTransitionedAutomaton) public

    transitionedAutomaton : Alphabet → DFA
    transitionedAutomaton c = record{automata = Deterministic.transitionedAutomaton(automata) c}

    wordTransitionedAutomaton : Word → DFA
    wordTransitionedAutomaton w = record{automata = Deterministic.wordTransitionedAutomaton(automata) w}

    postulate isFinal : State → Bool
    postulate isFinal-correctness : ∀{s} → IsTrue(isFinal s) ↔ (s ∈ Final)

    isWordAccepted : Word → Bool
    isWordAccepted(w) = isFinal(wordTransition(start)(w))

  pattern dfa {fin-Q} {fin-Σ} δ {δ-op} q₀ F = record{State-finite = fin-Q ; Alphabet-finite = fin-Σ ; automata = deterministic δ ⦃ δ-op ⦄ q₀ F}
