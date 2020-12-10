import      Lvl
open import Structure.Setoid.WithLvl
open import Type

module Automaton.TuringMachine where

open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Either as Either using (_‖_)
open import Data.Either.Equiv
open import Data.Option as Option
open import Data.Option.Functions as Option
open import Data.Option.Equiv
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Equiv
open import Data.List renaming (∅ to ε ; _⊰_ to _·_)
open import Data.List.Equiv
open import Functional
open import Logic
open import Relator.Equals.Proofs.Equivalence
open import Structure.Operator
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type.Size.Finite

private variable ℓₚ ℓₛ ℓₐ ℓₑₛ ℓₑₐ : Lvl.Level
private variable Alphabet : Type{ℓₐ}

data Direction : Type{Lvl.𝟎} where
  Backward : Direction
  Stay     : Direction
  Forward  : Direction
private instance _ = [≡]-equiv {T = Direction}

record Tape (Alphabet : Type{ℓₐ}) : Type{ℓₐ} where
  coinductive
  field
    back    : Tape(Alphabet)
    current : Alphabet
    front   : Tape(Alphabet)

  update : (Alphabet → Alphabet) → Tape(Alphabet)
  back   (update _) = back
  current(update f) = f(current)
  front  (update _) = front

stepBackward : Tape(Alphabet) → Tape(Alphabet)
Tape.back   (stepBackward t) = Tape.back(Tape.back t)
Tape.current(stepBackward t) = Tape.current(Tape.back t)
Tape.front  (stepBackward t) = t

stepForward : Tape(Alphabet) → Tape(Alphabet)
Tape.back   (stepForward t) = t
Tape.current(stepForward t) = Tape.current(Tape.front t)
Tape.front  (stepForward t) = Tape.front(Tape.front t)

stepInDirection : Direction → Tape(Alphabet) → Tape(Alphabet)
stepInDirection Backward = stepBackward
stepInDirection Stay     = id
stepInDirection Forward  = stepForward

module _ ⦃ equiv-alphabet : Equiv{ℓₑₐ}(Alphabet) ⦄ where
  step-inverseₗᵣ : ∀{t : Tape(Alphabet)} → (Tape.current(stepBackward(stepForward(t))) ≡ Tape.current(t))
  step-inverseₗᵣ = reflexivity(_≡_ ⦃ equiv-alphabet ⦄)

  step-inverseᵣₗ : ∀{t : Tape(Alphabet)} → (Tape.current(stepBackward(stepForward(t))) ≡ Tape.current(t))
  step-inverseᵣₗ = reflexivity(_≡_ ⦃ equiv-alphabet ⦄)

module _
  (State : Type{ℓₛ})    ⦃ equiv-state : Equiv{ℓₑₛ}(State) ⦄
  (Alphabet : Type{ℓₐ}) ⦃ equiv-alphabet : Equiv{ℓₑₐ}(Alphabet) ⦄
  where

  private instance _ = [≡]-equiv {T = Bool}

  -- Turing machine
  -- `State`      (Q)  is the set of states.
  -- `Alphabet`   (Σ)  is the set of symbols/the alphabet.
  -- `transition` (δ)  is the transition function.
  -- `start`      (q₀) is the start state.
  -- `Final`      (F)  is the subset of State which are the final/accepting states.
  record TuringMachine : Type{ℓₛ Lvl.⊔ ℓₑₐ Lvl.⊔ ℓₑₛ Lvl.⊔ ℓₐ Lvl.⊔ Lvl.𝐒(ℓₚ)} where
    constructor turingMachine
    field
      ⦃ State-finite ⦄              : Finite(State)
      ⦃ Alphabet-finite ⦄           : Finite(Alphabet)
      transition                    : State → Option(Alphabet) → Option(State ⨯ Alphabet ⨯ Direction)
      ⦃ transition-binaryOperator ⦄ : BinaryOperator(transition)
      start                         : State
      Final                         : State → Type{ℓₚ}
      ⦃ Final-unaryRelator ⦄        : UnaryRelator(Final)

    -- isFinal : State → Bool

  -- TODO: Not sure what the best (most easy to use) formalization of a TM would be or if this is correct
  Configuration = State ⨯ Tape(Option(Alphabet))
  module Configuration where
    step : TuringMachine{ℓₚ} → (Configuration → Option(Configuration))
    step tm (s , t) = Option.map (\(ns , nx , dir) → (ns , stepInDirection dir (Tape.update t (Some ∘ const nx)))) (TuringMachine.transition tm s (Tape.current t))
