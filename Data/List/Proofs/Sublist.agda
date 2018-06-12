import      Lvl
open import Type

module Data.List.Proofs.Sublist {ℓ₁ ℓ₂ : Lvl.Level} (T : Type{ℓ₂}) where

open import Functional
open import Data.List
open import Data.List.Proofs
open import Data.List.Relation.Sublist{ℓ₁}{ℓ₂}(T)
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂}

instance
  [⊑]-reflexivity : ∀{L} → (L ⊑ L)
  [⊑]-reflexivity {∅}     = empty
  [⊑]-reflexivity {a ⊰ L} = use([⊑]-reflexivity{L})

instance
  [⊑]-minimum : ∀{L} → (∅ ⊑ L)
  [⊑]-minimum {∅}     = empty
  [⊑]-minimum {a ⊰ L} = skip([⊑]-minimum{L})

instance
  [⊑]ᵣ-of-[++]ₗ : ∀{L₁ L₂} → (L₁ ⊑ (L₂ ++ L₁))
  [⊑]ᵣ-of-[++]ₗ {∅}{∅} = empty
  [⊑]ᵣ-of-[++]ₗ {L₁}{∅} = [⊑]-reflexivity
  -- [⊑]-of-[++]ₗ {L₁}{∅} = emptyᵣ -- Either this line or the first seems to be redundant
  [⊑]ᵣ-of-[++]ₗ {L₁}{a₂ ⊰ L₂} = skip{a₂}([⊑]ᵣ-of-[++]ₗ {L₁}{L₂})
