module Data.List.Decidable where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Tuple
open import Data.List
open import Data.List.Functions
open import Data.List.Equiv
open import Data.List.Proofs.Simple
open import Functional
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type
open import Type.Properties.Decidable
open import Type.Properties.Decidable.Proofs

private variable ℓ ℓₑ ℓₑₗ : Lvl.Level
private variable T : Type{ℓ}

module _
  ⦃ equiv      : Equiv{ℓₑ}(T) ⦄
  ⦃ equiv-list : Equiv{ℓₑₗ}(List(T)) ⦄
  ⦃ ext        : Extensionality(equiv-list) ⦄
  {_≡?_ : T → T → Bool}
  where

  _[==]_ = satisfiesAll₂(_≡?_) (const(const 𝐹)) (const(const 𝐹))

  instance
    [≡]-decider : ⦃ dec : Decider(2)(_≡_ {T = T})(_≡?_) ⦄ → Decider(2)(_≡_ {T = List(T)})(_[==]_)
    [≡]-decider {x = ∅}      {∅}      = true (reflexivity(_≡_))
    [≡]-decider {x = ∅}      {y ⊰ ys} = false [∅][⊰]-unequal
    [≡]-decider {x = x ⊰ xs} {∅}      = false ([∅][⊰]-unequal ∘ symmetry(_≡_))
    [≡]-decider {x = x ⊰ xs} {y ⊰ ys}
      rewrite satisfiesAll₂-step {_▫_ = _≡?_}{const(const 𝐹)}{const(const 𝐹)}{x}{xs}{y}{ys}
      = step{f = id} (true ∘ uncurry (congruence₂(_⊰_))) (false ∘ contrapositiveᵣ [⊰]-generalized-cancellation) (tuple-decider ⦃ dec-Q = [≡]-decider {x = xs} {ys} ⦄)
