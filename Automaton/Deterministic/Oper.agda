module Automaton.Deterministic.Oper where

open import Automaton.Deterministic
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
open import Structure.Setoid.WithLvl
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₚ ℓₚ₁ ℓₚ₂ : Lvl.Level
private variable Q Q₁ Q₂ State : Type{ℓ}
private variable Σ Σ₁ Σ₂ Alphabet : Type{ℓ}

module _ ⦃ equiv₁ : Equiv{ℓₑ₁}(Q₁) ⦄ ⦃ equiv₂ : Equiv{ℓₑ₂}(Q₂) ⦄ ⦃ equivₑ : Equiv{ℓₑ₃}(Σ) ⦄ where
  -- Automaton that accepts words accepted by both of the specified automatons
  _⨯_ : Deterministic{ℓₚ = ℓₚ₁}(Q₁)(Σ) → Deterministic{ℓₚ = ℓₚ₂}(Q₂)(Σ) → Deterministic(Q₁ ⨯' Q₂)(Σ)
  _⨯_ (deterministic δ₁ q₀₁ F₁) (deterministic δ₂ q₀₂ F₂) = deterministic δ ⦃ δ-op ⦄ q₀ F where
    δ : (Q₁ ⨯' Q₂) → Σ → (Q₁ ⨯' Q₂)
    δ(q₁ , q₂)(word) = (δ₁(q₁)(word) , δ₂(q₂)(word))

    instance
      δ-op : BinaryOperator(δ)
      BinaryOperator.congruence δ-op ([∧]-intro xyl xyr) cc = [∧]-intro (congruence₂(δ₁) xyl cc) (congruence₂(δ₂) xyr cc)

    q₀ : (Q₁ ⨯' Q₂)
    q₀ = (q₀₁ , q₀₂)

    F : PredSet(Q₁ ⨯' Q₂)
    F = PredSet.intro (\{(q₁ , q₂) → (q₁ ∈ F₁) ∧ (q₂ ∈ F₂)})
      ⦃ [∧]-unaryRelator
        ⦃ rel-P = [∘]-unaryRelator ⦃ rel = PredSet.preserve-equiv F₁ ⦄ ⦄
        ⦃ rel-Q = [∘]-unaryRelator ⦃ rel = PredSet.preserve-equiv F₂ ⦄ ⦄
      ⦄

  -- Automaton that accepts words accepted by any of the specified automatons
  _+_ : Deterministic{ℓₚ = ℓₚ₁}(Q₁)(Σ) → Deterministic{ℓₚ = ℓₚ₂}(Q₂)(Σ) → Deterministic(Q₁ ⨯' Q₂)(Σ)
  _+_ (deterministic δ₁ q₀₁ F₁) (deterministic δ₂ q₀₂ F₂) = deterministic δ q₀ F where
    δ : (Q₁ ⨯' Q₂) → Σ → (Q₁ ⨯' Q₂)
    δ(q₀₁ , q₀₂)(word) = (δ₁(q₀₁)(word) , δ₂(q₀₂)(word))

    instance
      δ-op : BinaryOperator(δ)
      BinaryOperator.congruence δ-op ([∧]-intro xyl xyr) cc = [∧]-intro (congruence₂(δ₁) xyl cc) (congruence₂(δ₂) xyr cc)

    q₀ : (Q₁ ⨯' Q₂)
    q₀ = (q₀₁ , q₀₂)

    F : PredSet(Q₁ ⨯' Q₂)
    F = PredSet.intro (\{(q₁ , q₂) → (q₁ ∈ F₁) ∨ (q₂ ∈ F₂)})
      ⦃ [∨]-unaryRelator
        ⦃ rel-P = [∘]-unaryRelator ⦃ rel = PredSet.preserve-equiv F₁ ⦄ ⦄
        ⦃ rel-Q = [∘]-unaryRelator ⦃ rel = PredSet.preserve-equiv F₂ ⦄ ⦄
      ⦄

module _ ⦃ equiv : Equiv{ℓₑ}(Q) ⦄ ⦃ equivₑ : Equiv{ℓₑ₃}(Σ) ⦄ where
  -- Automaton that accepts words not accepted by the specified automaton
  ∁_ : Deterministic{ℓₚ = ℓₚ}(Q)(Σ) → Deterministic(Q)(Σ)
  ∁_ (deterministic δ q₀ F) = deterministic δ q₀ (PredSet.∁ F)
