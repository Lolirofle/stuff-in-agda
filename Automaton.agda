import      Lvl
open import Structure.Set
open import Structure.Setoid
open import Type

module Automaton
  {ℓₐ ℓₑₐ} (Alphabet : Type{ℓₐ}) ⦃ equiv-alphabet : Equiv{ℓₑₐ}(Alphabet) ⦄
  {ℓᵢ ℓₑᵢ} (Input : Type{ℓᵢ}) ⦃ equiv-Input : Equiv{ℓₑᵢ}(Input) ⦄
  {ℓₒ ℓₑₒ} (Output : Type{ℓₒ}) ⦃ equiv-Output : Equiv{ℓₑₒ}(Output) ⦄
  where

open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator
open import Structure.Relator

-- TODO: Some kind of useful generalisation on different automata? Is it possible to express any useful rules?
record Automaton{ℓc ℓₑc} : Type{ℓₐ Lvl.⊔ ℓₑₐ Lvl.⊔ ℓᵢ Lvl.⊔ ℓₑᵢ Lvl.⊔ ℓₒ Lvl.⊔ ℓₑₒ Lvl.⊔ Lvl.𝐒(ℓc Lvl.⊔ ℓₑc)} where
  field
    Configuration : Type{ℓc}
  field
    initial : Input → Configuration
    transition : Alphabet → Configuration → Configuration
    input : Configuration → Input
    output : Configuration → Output
  field
    ⦃ equiv-configuration ⦄ : Equiv{ℓₑc}(Configuration)
    ⦃ transition-function ⦄ : BinaryOperator(transition)
    ⦃ initial-function ⦄ : Function(initial)
    ⦃ input-function ⦄ : Function(input)
    ⦃ output-function ⦄ : Function(output)
    ⦃ initial-input-inverse ⦄ : Inverse(initial)(input)
