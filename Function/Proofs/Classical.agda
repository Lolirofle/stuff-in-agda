module Function.Proofs.Classical where

open import Function.Proofs
open import Functional
open import Logic.Classical
open import Logic.Propositional
import      Lvl
open import Structure.Function.Domain
open import Structure.Setoid
open import Type
open import Type.Dependent.Sigma
open import Type.Properties.Empty
open import Type.Properties.Empty.Proofs
open import Type.Properties.MereProposition

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  id-constant-by-empty : ⦃ empty : IsEmpty{ℓ}(T) ⦄ → Constant(id{T = T})
  id-constant-by-empty = intro \{x} → emptyAny x

  id-constant-by-prop : ⦃ prop : MereProposition(T) ⦄ → Constant(id{T = T})
  id-constant-by-prop = intro(uniqueness T)

  id-constant-by-negation : (¬ T) → Constant(id{T = T})
  id-constant-by-negation n = intro \{x} → [⊥]-elim(n x)

  constant-operator-by-classical : ⦃ classical : Classical(T) ⦄ → Σ(T → T) Constant
  constant-operator-by-classical with excluded-middle(T)
  ... | [∨]-introₗ a  = intro(const a) const-constant
  ... | [∨]-introᵣ na = intro id       (id-constant-by-negation na)
