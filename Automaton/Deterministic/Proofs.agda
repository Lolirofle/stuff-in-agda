import      Lvl
open import Structure.Setoid
open import Type

module Automaton.Deterministic.Proofs
  {ℓₐ ℓₑₐ} {Alphabet : Type{ℓₐ}} ⦃ equiv-alphabet : Equiv{ℓₑₐ}(Alphabet) ⦄
  {ℓₛ ℓₑₛ} {State : Type{ℓₛ}} ⦃ equiv-state : Equiv{ℓₑₛ}(State) ⦄
  where

open import Automaton.Deterministic(Alphabet) ⦃ equiv-alphabet ⦄
open import Data.List.Equiv
open import Data.List.Functions using (postpend ; _++_)
open import Data.List.Proofs
import      Structure.Function.Names as Names
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity

private variable ℓₑₗ ℓₚ : Lvl.Level

module _ {d : Deterministic(State){ℓₚ}} where
  open Deterministic d

  module _ ⦃ equiv-Word : Equiv{ℓₑₗ}(Word) ⦄ ⦃ ext-Word : Extensionality(equiv-Word) ⦄ where
    instance
      wordTransition-function : BinaryOperator(wordTransition)
      wordTransition-function = intro p where
        p : Names.Congruence₂(wordTransition)
        p {x₂ = ε}       {y₂ = ε}       xy1 xy2 = xy1
        p {x₂ = ε}       {c₂ · w₂}      xy1 xy2 with () ← [∅][⊰]-unequal xy2
        p {x₂ = c₁ · w₁} {ε}            xy1 xy2 with () ← [∅][⊰]-unequal (symmetry(_≡_) xy2)
        p {x₂ = c₁ · w₁} {y₂ = c₂ · w₂} xy1 xy2 = p{x₂ = w₁}{y₂ = w₂} (congruence₂(transition) xy1 ([⊰]-generalized-cancellationᵣ xy2)) ([⊰]-generalized-cancellationₗ xy2)

    wordTransition-postpend : ∀{s}{w}{a} → ((wordTransition s (postpend a w)) ≡ transition (wordTransition s w) a)
    wordTransition-postpend {s}{ε}    {a} = reflexivity(_≡_) {x = transition s a}
    wordTransition-postpend {s}{x · w}{a} = wordTransition-postpend {transition s x}{w}{a}

    -- Note: ((swap ∘ wordTransition) d (w₁ ++ w₂) ⊜ (swap ∘ wordTransition) d w₂ ∘ (swap ∘ wordTransition) d w₁)
    wordTransition-[++] : ∀{s}{w₁ w₂} → (wordTransition s (w₁ ++ w₂) ≡ (wordTransition (wordTransition s w₁) w₂))
    wordTransition-[++] {s = s} {w₁ = w₁} {w₂ = ε} =
      wordTransition s (w₁ ++ ε)             🝖[ _≡_ ]-[ congruence₂-₂(wordTransition)(s) (identityᵣ(_++_)(ε) {w₁}) ]
      wordTransition s w₁                    🝖[ _≡_ ]-[]
      wordTransition (wordTransition s w₁) ε 🝖-end
    wordTransition-[++] {s = s} {w₁ = w₁} {w₂ = c₂ · w₂} =
      wordTransition s (w₁ ++ (c₂ · w₂))                      🝖[ _≡_ ]-[ congruence₂-₂(wordTransition)(s) ([++]-middle-prepend-postpend{l₁ = w₁}) ]-sym
      wordTransition s (postpend c₂ w₁ ++ w₂)                 🝖[ _≡_ ]-[ wordTransition-[++] {s = s}{w₁ = postpend c₂ w₁}{w₂ = w₂} ]
      wordTransition (wordTransition s (postpend c₂ w₁)) w₂   🝖[ _≡_ ]-[ congruence₂-₁(wordTransition)(w₂) (wordTransition-postpend{s = s}{w = w₁}) ]
      wordTransition (transition (wordTransition s w₁) c₂) w₂ 🝖-end
