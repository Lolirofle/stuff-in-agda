module Sets.BoolSet.Proofs{ℓ₁} where

open import Data.Boolean
open import Data.Boolean.Proofs
open import Functional
open import Logic.Propositional
open import Sets.BoolSet{ℓ₁}
open import Type

module _ {ℓ₂}{T : Type{ℓ₂}} where
  [∈]-in-[∪] : ∀{a : T}{S₁ S₂ : BoolSet(T)} → (a ∈ S₁) → (a ∈ (S₁ ∪ S₂))
  [∈]-in-[∪] proof-a = [∨]-introₗ-[𝑇] proof-a

  [∈]-in-[∩] : ∀{a : T}{S₁ S₂ : BoolSet(T)} → (a ∈ S₁) → (a ∈ S₂) → (a ∈ (S₁ ∩ S₂))
  [∈]-in-[∩] proof-a₁ proof-a₂ = [∧]-intro-[𝑇] proof-a₁ proof-a₂

  [∈]-in-[∖] : ∀{a : T}{S₁ S₂ : BoolSet(T)} → (a ∈ S₁) → (a ∉ S₂) → (a ∈ (S₁ ∖ S₂))
  [∈]-in-[∖] proof-a₁ proof-a₂ = [∧]-intro-[𝑇] proof-a₁ proof-a₂

  [∈]-in-[∁] : ∀{a : T}{S : BoolSet(T)} → (a ∉ S) → (a ∈ (∁ S))
  [∈]-in-[∁] = id
