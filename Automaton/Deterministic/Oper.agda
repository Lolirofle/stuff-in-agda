import      Lvl
open import Structure.Setoid
open import Type

module Automaton.Deterministic.Oper
  {ℓₐ ℓₑₐ} (Alphabet : Type{ℓₐ}) ⦃ equiv-alphabet : Equiv{ℓₑₐ}(Alphabet) ⦄
  where

open import Automaton.Deterministic(Alphabet) ⦃ equiv-alphabet ⦄
open import Logic.Propositional
import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.List renaming (∅ to [])
open import Data.Tuple as Tuple using (_,_) renaming (_⨯_ to _⨯'_)
open import Data.Tuple.Equivalence
open import Functional
open import Sets.ExtensionalPredicateSet as PredSet using (PredSet ; _∈_)
open import Structure.Operator
open import Structure.Relator.Proofs
open import Structure.Setoid
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₚ ℓₚ₁ ℓₚ₂ : Lvl.Level
private variable Q Q₁ Q₂ State : Type{ℓ}
private Σ = Alphabet

module _ ⦃ equiv₁ : Equiv{ℓₑ₁}(Q₁) ⦄ ⦃ equiv₂ : Equiv{ℓₑ₂}(Q₂) ⦄ where
  -- Automaton that accepts words accepted by both of the specified automatons.
  _⨯_ : Deterministic(Q₁){ℓₚ₁} → Deterministic(Q₂){ℓₚ₂} → Deterministic(Q₁ ⨯' Q₂)
  _⨯_ (deterministic δ₁ q₀₁ F₁) (deterministic δ₂ q₀₂ F₂) = deterministic δ q₀ F where
    δ : (Q₁ ⨯' Q₂) → Σ → (Q₁ ⨯' Q₂)
    δ(q₁ , q₂)(word) = (δ₁(q₁)(word) , δ₂(q₂)(word))

    instance
      δ-op : BinaryOperator(δ)
      δ-op = intro \([∧]-intro xyl xyr) cc → [∧]-intro (congruence₂(δ₁) xyl cc) (congruence₂(δ₂) xyr cc)

    q₀ : (Q₁ ⨯' Q₂)
    q₀ = (q₀₁ , q₀₂)

    F : PredSet(Q₁ ⨯' Q₂)
    F = PredSet.intro (\{(q₁ , q₂) → (q₁ ∈ F₁) ∧ (q₂ ∈ F₂)})
      ⦃ [∧]-unaryRelator
        ⦃ rel-P = [∘]-unaryRelator ⦃ rel = PredSet.preserve-equiv F₁ ⦄ ⦄
        ⦃ rel-Q = [∘]-unaryRelator ⦃ rel = PredSet.preserve-equiv F₂ ⦄ ⦄
      ⦄

  -- Automaton that accepts words accepted by any of the specified automatons.
  _+_ : Deterministic(Q₁){ℓₚ₁} → Deterministic(Q₂){ℓₚ₂} → Deterministic(Q₁ ⨯' Q₂)
  _+_ (deterministic δ₁ q₀₁ F₁) (deterministic δ₂ q₀₂ F₂) = deterministic δ q₀ F where
    δ : (Q₁ ⨯' Q₂) → Σ → (Q₁ ⨯' Q₂)
    δ(q₀₁ , q₀₂)(word) = (δ₁(q₀₁)(word) , δ₂(q₀₂)(word))

    instance
      δ-op : BinaryOperator(δ)
      δ-op = intro \([∧]-intro xyl xyr) cc → [∧]-intro (congruence₂(δ₁) xyl cc) (congruence₂(δ₂) xyr cc)

    q₀ : (Q₁ ⨯' Q₂)
    q₀ = (q₀₁ , q₀₂)

    F : PredSet(Q₁ ⨯' Q₂)
    F = PredSet.intro (\{(q₁ , q₂) → (q₁ ∈ F₁) ∨ (q₂ ∈ F₂)})
      ⦃ [∨]-unaryRelator
        ⦃ rel-P = [∘]-unaryRelator ⦃ rel = PredSet.preserve-equiv F₁ ⦄ ⦄
        ⦃ rel-Q = [∘]-unaryRelator ⦃ rel = PredSet.preserve-equiv F₂ ⦄ ⦄
      ⦄

module _ ⦃ equiv : Equiv{ℓₑ}(Q) ⦄ where
  -- Automaton that accepts words not accepted by the specified automaton.
  ∁_ : Deterministic(Q){ℓₚ} → Deterministic(Q)
  ∁_ (deterministic δ q₀ F) = deterministic δ q₀ (PredSet.∁ F)

  step : Alphabet → Deterministic(Q){ℓₚ} → Deterministic(Q)
  step c (deterministic δ q₀ F) = deterministic δ (δ q₀ c) F

  stepWord : Word → Deterministic(Q){ℓₚ} → Deterministic(Q)
  stepWord w d@(deterministic δ q₀ F) =
    let open Deterministic.LetterNotation d using (δ̂)
    in deterministic δ (δ̂ q₀ w) F
