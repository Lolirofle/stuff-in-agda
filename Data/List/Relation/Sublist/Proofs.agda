import      Lvl
open import Type

module Data.List.Relation.Sublist.Proofs {ℓ} {T : Type{ℓ}} where

open import Functional
open import Data.List hiding (skip)
open import Data.List.Proofs
open import Data.List.Relation.Sublist{ℓ}{T}
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Equals

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
  [⊑]ᵣ-of-[++]ₗ {L₁}{∅}       = [⊑]-reflexivity
  [⊑]ᵣ-of-[++]ₗ {L₁}{a₂ ⊰ L₂} = skip{a₂}([⊑]ᵣ-of-[++]ₗ {L₁}{L₂})
