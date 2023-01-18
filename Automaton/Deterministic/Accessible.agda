import      Lvl
open import Structure.Setoid
open import Type

module Automaton.Deterministic.Accessible
  {ℓₐ ℓₑₐ} {Alphabet : Type{ℓₐ}} ⦃ equiv-alphabet : Equiv{ℓₑₐ}(Alphabet) ⦄
  where

open import Automaton.Deterministic(Alphabet) ⦃ equiv-alphabet ⦄
open import Automaton.Deterministic.Proofs ⦃ equiv-alphabet ⦄
open import Data.List.Equiv
open import Data.List.Functions using (postpend ; _++_)
open import Logic.Predicate
open import Logic.Predicate.Equiv
open import Sets.ExtensionalPredicateSet using (PredSet ; intro ; _∈_ ; _∋_ ; ⊶ ; [∋]-binaryRelator)
open import Structure.Operator
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Transitivity

private variable ℓₛ ℓₑₛ ℓₚ ℓₑₗ : Lvl.Level

module _ {State : Type{ℓₛ}} ⦃ equiv-state : Equiv{ℓₑₛ}(State) ⦄ where
  module _ (d : Deterministic(State){ℓₚ}) where
    open Deterministic d

    -- The subset of State which are the accessible states from the start state by chained transitions.
    Accessible : PredSet(State)
    Accessible = ⊶(wordTransition start)

    instance
      accessible-start : (start ∈ Accessible)
      accessible-start = [∃]-intro ε ⦃ reflexivity(_≡_) {x = start} ⦄

    module _ ⦃ equiv-Word : Equiv{ℓₑₗ}(Word) ⦄ ⦃ ext-Word : Extensionality(equiv-Word) ⦄ where
      instance
        accessible-transition : ∀{s}{a} → ⦃ _ : (s ∈ Accessible) ⦄ → (transition s a ∈ Accessible)
        accessible-transition {s} {a = a} ⦃ [∃]-intro w ⦃ p ⦄ ⦄ = [∃]-intro (postpend a w)
          ⦃
            wordTransition start (postpend a w)   🝖-[ wordTransition-postpend {d = d}{s = start}{w = w}{a = a} ]
            transition (wordTransition start w) a 🝖-[ congruence₂-₁(transition) a p ]
            transition s a                        🝖-end
          ⦄

  module _ where
    open Deterministic

    module _ ⦃ equiv-Word : Equiv{ℓₑₗ}(Word) ⦄ ⦃ ext-Word : Extensionality(equiv-Word) ⦄ where
      accessibleAutomaton : (d : Deterministic(State){ℓₚ}) → Deterministic(∃(_∈ Accessible d))
      transition (accessibleAutomaton d) ([∃]-intro s) a = [∃]-intro (transition d s a) ⦃ accessible-transition d ⦄
      BinaryOperator.congruence (transition-binaryOperator (accessibleAutomaton d)) = congruence₂(transition d)
      start (accessibleAutomaton d) = [∃]-intro (start d) ⦃ accessible-start d ⦄
      Final (accessibleAutomaton d) PredSet.∋ [∃]-intro s = s ∈ Final d
      PredSet.preserve-equiv (Final (accessibleAutomaton d)) = UnaryRelator-introᵣ \{ {[∃]-intro x} {[∃]-intro y} → substitute₂-₂ᵣ(_∋_)(Final d) {x}{y} }
