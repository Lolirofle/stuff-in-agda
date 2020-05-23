import      Lvl
open import Structure.Setoid.WithLvl
open import Type

module Automaton.Deterministic where

open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.List renaming (∅ to ε ; _⊰_ to _·_)
-- open import Data.List.Proofs
open import Functional
open import Logic
open import Logic.Predicate
open import Logic.Predicate.Equiv
open import Relator.Equals.Proofs.Equivalence
open import Sets.ExtensionalPredicateSet using (PredSet ; intro ; _∈_ ; _∋_ ; ⊶ ; [∋]-binaryRelator)
open import Structure.Operator
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Transitivity

-- According to http://www.cse.chalmers.se/edu/course/TMV027/lec5.pdf

module _ {ℓₚ ℓₛ ℓₑ ℓₐ} (State : Type{ℓₛ}) ⦃ equiv-state : Equiv{ℓₑ}(State) ⦄ (Alphabet : Type{ℓₐ}) where
  private instance _ = [≡]-equiv {T = Alphabet}
  private instance _ = [≡]-equiv {T = List(Alphabet)}

  -- Deterministic Automata
  -- `State`      (Q)  is the set of states.
  -- `Alphabet`   (Σ)  is the set of symbols/the alphabet.
  -- `transition` (δ)  is the transition function.
  -- `start`      (q₀) is the start state.
  -- `Final`      (F)  is the subset of State which are the final/accepting states.
  record Deterministic : Type{ℓₛ Lvl.⊔ ℓₑ Lvl.⊔ ℓₐ Lvl.⊔ Lvl.𝐒(ℓₚ)} where
    constructor deterministic
    field
      transition : State → Alphabet → State
      ⦃ transition-binaryOperator ⦄ : BinaryOperator(transition)
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

    automatonTransition : Alphabet → Deterministic
    transition (automatonTransition _) = transition
    start      (automatonTransition c) = transition start c
    Final      (automatonTransition _) = Final

    automatonTransitionWord : Word → Deterministic
    transition (automatonTransitionWord _) = transition
    start      (automatonTransitionWord w) = transitionWord start w
    Final      (automatonTransitionWord _) = Final

    instance
      transitionWord-binaryOperator : BinaryOperator(transitionWord)
      BinaryOperator.congruence transitionWord-binaryOperator xy1 {ε} {ε} xy2 = xy1
      BinaryOperator.congruence transitionWord-binaryOperator xy1 {c₁ · w₁} {c₂ · w₂} xy2 = {!!} -- BinaryOperator.congruence transitionWord-binaryOperator {!!} {w₁} {w₂} {!!}

  open Deterministic

  transitionWord-postpend : ∀{d}{s}{w}{a} → ((transitionWord d s (postpend a w)) ≡ transition d (transitionWord d s w) a)
  transitionWord-postpend {d}{s}{ε}    {a} = reflexivity(_≡_) {x = transition d s a}
  transitionWord-postpend {d}{s}{x · w}{a} = transitionWord-postpend {d}{transition d s x}{w}{a}

  instance
    accessible-start : ∀{d} → (start d ∈ Accessible d)
    accessible-start {d} = [∃]-intro ε ⦃ reflexivity(_≡_) {x = start d} ⦄

  instance
    accessible-transition : ∀{d}{s}{a} → ⦃ _ : (s ∈ Accessible d) ⦄ → (transition d s a ∈ Accessible d)
    accessible-transition {d} {s} {a = a} ⦃ [∃]-intro w ⦃ p ⦄ ⦄ = [∃]-intro (postpend a w)
      ⦃
        transitionWord d (start d) (postpend a w)     🝖-[ transitionWord-postpend{d}{start d}{w}{a} ]
        transition d (transitionWord d (start d) w) a 🝖-[ congruence₂ₗ(transition d) a p ]
        transition d s a                              🝖-end
      ⦄

module _ {ℓₚ ℓₛ ℓₐ} (State : Type{ℓₛ}) ⦃ equiv-state : Equiv{ℓₚ}(State) ⦄ (Alphabet : Type{ℓₐ}) where
  open Deterministic

  private instance _ = [≡]-equiv {T = Alphabet}
  private instance _ = [≡]-equiv {T = List(Alphabet)}

  accessibleAutomaton : (d : Deterministic{ℓₚ}(State)(Alphabet)) → Deterministic{ℓₚ}(∃(_∈ Accessible d)) (Alphabet)
  transition (accessibleAutomaton d) ([∃]-intro s) a = [∃]-intro (transition d s a) ⦃ accessible-transition State Alphabet ⦄
  BinaryOperator.congruence (transition-binaryOperator (accessibleAutomaton d)) = congruence₂(transition d)
  start (accessibleAutomaton d) = [∃]-intro (start d) ⦃ accessible-start State Alphabet ⦄
  Final (accessibleAutomaton d) PredSet.∋ [∃]-intro s = s ∈ Final d
  UnaryRelator.substitution (PredSet.preserve-equiv (Final (accessibleAutomaton d))) {[∃]-intro x} {[∃]-intro y} = substitute₂ᵣ(_∋_) {intro (_∈ Final d)}
