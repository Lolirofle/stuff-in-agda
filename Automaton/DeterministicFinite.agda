module Automaton.DeterministicFinite where

open import Boolean
import      Boolean.Operators
open        Boolean.Operators.Programming
open import Data renaming(_⨯_ to _⨯'_)
open import FormalLanguage.Language
open import Functional
open import List renaming (∅ to [])

-- According to http://www.cse.chalmers.se/edu/course/TMV027/lec5.pdf

-- Deterministic Finite Automata
-- `state`        is Q  (the finite set of states)
-- `alphabet`     is ∑  (the finite set of symbols/the alphabet)
-- `transition`   is δ  (the total transition function)
-- `startState`   is q₀ (the start state)
-- `isFinalState` is (x ↦ elem x F) (the function that checks whether a state is a final/accepting state)
record DFA (State : Set) (Alphabet : Set) : Set where
  constructor Dfa
  field
    transition   : State → Alphabet → State
    startState   : State
    isFinalState : State → Bool

  states   = State
  alphabet = Alphabet

  wordTransition : State → Word(Alphabet) → State
  wordTransition initialState []            = initialState
  wordTransition initialState (head ⊰ tail) = wordTransition state tail where
    state = transition initialState head

  Q  = State
  ∑  = Alphabet
  δ  = transition
  δ̂  = wordTransition
  q₀ = startState
  F  = isFinalState

  -- If when the input is read from the start state the automaton stops in a final state, it accepts the word.
  isWordAccepted : Word(∑) → Bool
  isWordAccepted word = F(δ̂(q₀)(word))

-- The language accepted by a DFA.
-- This is a lingvistic interpretation of an automaton, that it is a grammar of the language.
-- A language accepts the empty word when the start state is a final state.
-- The language of a suffix is the transition function applied to the start state.
language : ∀{Q}{∑}{s} → DFA(Q)(∑) → Language(∑){s}
Language.accepts-ε   (language(Dfa δ q₀ F)) = F(q₀)
Language.suffix-lang (language(Dfa δ q₀ F)) = (c ↦ language(Dfa δ (δ(q₀)(c)) F))

_⨯_ : ∀{Q₁ Q₂}{∑} → DFA(Q₁)(∑) → DFA(Q₂)(∑) → DFA(Q₁ ⨯' Q₂)(∑)
_⨯_ {Q₁}{Q₂}{∑} (Dfa δ₁ q₀₁ F₁) (Dfa δ₂ q₀₂ F₂) = Dfa δ q₀ F where
  δ : (Q₁ ⨯' Q₂) → ∑ → (Q₁ ⨯' Q₂)
  δ(q₀₁ , q₀₂)(word) = (δ₁(q₀₁)(word) , δ₂(q₀₂)(word))

  q₀ : (Q₁ ⨯' Q₂)
  q₀ = (q₀₁ , q₀₂)

  F : (Q₁ ⨯' Q₂) → Bool
  F(q₁ , q₂) = F₁(q₁) && F₂(q₂)

_+_ : ∀{Q₁ Q₂}{∑} → DFA(Q₁)(∑) → DFA(Q₂)(∑) → DFA(Q₁ ⨯' Q₂)(∑)
_+_ {Q₁}{Q₂}{∑} (Dfa δ₁ q₀₁ F₁) (Dfa δ₂ q₀₂ F₂) = Dfa δ q₀ F where
  δ : (Q₁ ⨯' Q₂) → ∑ → (Q₁ ⨯' Q₂)
  δ(q₀₁ , q₀₂)(word) = (δ₁(q₀₁)(word) , δ₂(q₀₂)(word))

  q₀ : (Q₁ ⨯' Q₂)
  q₀ = (q₀₁ , q₀₂)

  F : (Q₁ ⨯' Q₂) → Bool
  F(q₁ , q₂) = F₁(q₁) || F₂(q₂)

∁_ : ∀{Q}{∑} → DFA(Q)(∑) → DFA(Q)(∑)
∁_ (Dfa δ q₀ F) = Dfa δ q₀ ((!_) ∘ F)
