import      Lvl
open import Structure.Setoid.WithLvl
open import Type

module Automaton.Deterministic where

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

-- According to http://www.cse.chalmers.se/edu/course/TMV027/lec5.pdf

private variable ℓₚ ℓₛ ℓₑ₁ ℓₐ ℓₑ₂ : Lvl.Level

module _
  {ℓₚ}
  (State : Type{ℓₛ}) ⦃ equiv-state : Equiv{ℓₑ₁}(State) ⦄
  (Alphabet : Type{ℓₐ}) ⦃ equiv-alphabet : Equiv{ℓₑ₂}(Alphabet) ⦄
  where

  -- Deterministic Automata
  -- `State`      (Q)  is the set of states.
  -- `Alphabet`   (Σ)  is the set of symbols/the alphabet.
  -- `transition` (δ)  is the transition function.
  -- `start`      (q₀) is the start state.
  -- `Final`      (F)  is the subset of State which are the final/accepting states.
  record Deterministic : Type{ℓₛ Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓₑ₂ Lvl.⊔ ℓₐ Lvl.⊔ Lvl.𝐒(ℓₚ)} where
    constructor deterministic
    field
      transition : State → Alphabet → State
      ⦃ transition-binaryOperator ⦄ : BinaryOperator(transition)
      start      : State
      Final      : PredSet{ℓₚ}(State)

    Word = List(Alphabet)

    -- Chained transition using a word (list of characters).
    wordTransition : State → Word → State
    wordTransition initialState ε       = initialState
    wordTransition initialState (a · l) = wordTransition (transition initialState a) l

    module LetterNotation where
      Q  = State
      Σ  = Alphabet
      δ  = transition
      δ̂  = wordTransition
      q₀ = start
      F  = Final

    -- A word is accepted by the automaton when it can transition from the start state to a final state.
    AcceptsWord : Word → Stmt
    AcceptsWord = (_∈ Final) ∘ wordTransition start

    transitionedAutomaton : Alphabet → Deterministic
    transition (transitionedAutomaton _) = transition
    start      (transitionedAutomaton c) = transition start c
    Final      (transitionedAutomaton _) = Final

    wordTransitionedAutomaton : Word → Deterministic
    transition (wordTransitionedAutomaton _) = transition
    start      (wordTransitionedAutomaton w) = wordTransition start w
    Final      (wordTransitionedAutomaton _) = Final

module _
  {State : Type{ℓₛ}} ⦃ equiv-state : Equiv{ℓₑ₁}(State) ⦄
  {Alphabet : Type{ℓₐ}} ⦃ equiv-alphabet : Equiv{ℓₑ₂}(Alphabet) ⦄
  {d : Deterministic{ℓₚ = ℓₚ}(State)(Alphabet)}
  where

  open import Data.List.Equiv.Correctness
  open import Structure.Operator.Properties
  open import Syntax.Transitivity

  open Deterministic(d)

  instance
    wordTransition-binaryOperator : BinaryOperator(wordTransition)
    wordTransition-binaryOperator = intro p where
      p : Names.Congruence₂(wordTransition)
      p {x₂ = ε}       {y₂ = ε}       xy1 xy2 = xy1
      p {x₂ = c₁ · w₁} {y₂ = c₂ · w₂} xy1 xy2 = p{x₂ = w₁}{y₂ = w₂} (congruence₂(transition) xy1 ([⊰]-generalized-cancellationᵣ xy2)) ([⊰]-generalized-cancellationₗ xy2)

  wordTransition-postpend : ∀{s}{w}{a} → ((wordTransition s (postpend a w)) ≡ transition (wordTransition s w) a)
  wordTransition-postpend {s}{ε}    {a} = reflexivity(_≡_) {x = transition s a}
  wordTransition-postpend {s}{x · w}{a} = wordTransition-postpend {transition s x}{w}{a}

  -- Note: ((swap ∘ wordTransition) d (w₁ ++ w₂) ⊜ (swap ∘ wordTransition) d w₂ ∘ (swap ∘ wordTransition) d w₁)
  wordTransition-[++] : ∀{s}{w₁ w₂} → (wordTransition s (w₁ ++ w₂) ≡ (wordTransition (wordTransition s w₁) w₂))
  wordTransition-[++] {s = s} {w₁ = w₁} {w₂ = ε} =
    wordTransition s (w₁ ++ ε)             🝖[ _≡_ ]-[ congruence₂ᵣ(wordTransition)(s) (identityᵣ(_++_)(ε) {w₁}) ]
    wordTransition s w₁                    🝖[ _≡_ ]-[]
    wordTransition (wordTransition s w₁) ε 🝖-end
  wordTransition-[++] {s = s} {w₁ = w₁} {w₂ = c₂ · w₂} =
    wordTransition s (w₁ ++ (c₂ · w₂))                      🝖[ _≡_ ]-[ congruence₂ᵣ(wordTransition)(s) ([++]-middle-prepend-postpend{l₁ = w₁}) ]-sym
    wordTransition s (postpend c₂ w₁ ++ w₂)                 🝖[ _≡_ ]-[ wordTransition-[++] {s = s}{w₁ = postpend c₂ w₁}{w₂ = w₂} ]
    wordTransition (wordTransition s (postpend c₂ w₁)) w₂   🝖[ _≡_ ]-[ congruence₂ₗ(wordTransition)(w₂) (wordTransition-postpend{s = s}{w = w₁}) ]
    wordTransition (transition (wordTransition s w₁) c₂) w₂ 🝖-end
