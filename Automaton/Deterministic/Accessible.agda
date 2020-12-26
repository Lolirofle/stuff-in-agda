import      Lvl
open import Structure.Setoid
open import Type

module Automaton.Deterministic.Accessible where

open import Automaton.Deterministic
open import Data.List renaming (∅ to ε ; _⊰_ to _·_)
open import Data.List.Functions using (postpend ; _++_)
open import Logic.Predicate
open import Logic.Predicate.Equiv
open import Sets.ExtensionalPredicateSet using (PredSet ; intro ; _∈_ ; _∋_ ; ⊶ ; [∋]-binaryRelator)
open import Structure.Operator
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Transitivity

private variable ℓₚ ℓₛ ℓₑ₁ ℓₐ ℓₑ₂ : Lvl.Level

module _
  {State : Type{ℓₛ}} ⦃ equiv-state : Equiv{ℓₑ₁}(State) ⦄
  {Alphabet : Type{ℓₐ}} ⦃ equiv-alphabet : Equiv{ℓₑ₂}(Alphabet) ⦄
  where

  module _ (d : Deterministic{ℓₚ = ℓₚ}(State)(Alphabet)) where
    open Deterministic(d)

    -- The subset of State which are the accessible states from the start state by chained transitions.
    Accessible : PredSet(State)
    Accessible = ⊶(wordTransition start)

    instance
      accessible-start : (start ∈ Accessible)
      accessible-start = [∃]-intro ε ⦃ reflexivity(_≡_) {x = start} ⦄

    instance
      accessible-transition : ∀{s}{a} → ⦃ _ : (s ∈ Accessible) ⦄ → (transition s a ∈ Accessible)
      accessible-transition {s} {a = a} ⦃ [∃]-intro w ⦃ p ⦄ ⦄ = [∃]-intro (postpend a w)
        ⦃
          wordTransition start (postpend a w)   🝖-[ wordTransition-postpend {d = d} {start}{w}{a} ]
          transition (wordTransition start w) a 🝖-[ congruence₂ₗ(transition) a p ]
          transition s a                        🝖-end
        ⦄

  module _ where
    open Deterministic

    accessibleAutomaton : (d : Deterministic{ℓₚ = ℓₚ}(State)(Alphabet)) → Deterministic(∃(_∈ Accessible d)) (Alphabet)
    transition (accessibleAutomaton d) ([∃]-intro s) a = [∃]-intro (transition d s a) ⦃ accessible-transition d ⦄
    BinaryOperator.congruence (transition-binaryOperator (accessibleAutomaton d)) = congruence₂(transition d)
    start (accessibleAutomaton d) = [∃]-intro (start d) ⦃ accessible-start d ⦄
    Final (accessibleAutomaton d) PredSet.∋ [∃]-intro s = s ∈ Final d
    UnaryRelator.substitution (PredSet.preserve-equiv (Final (accessibleAutomaton d))) {[∃]-intro x} {[∃]-intro y} = substitute₂ᵣ(_∋_) {intro (_∈ Final d)}
