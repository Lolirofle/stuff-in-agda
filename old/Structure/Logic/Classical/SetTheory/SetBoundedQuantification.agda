import Structure.Logic.Classical.NaturalDeduction

-- TODO: MAybe rename to SetBoundedQuantification
module Structure.Logic.Classical.SetTheory.SetBoundedQuantification {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic : _ ⦄ (_∈_ : Domain → Domain → Formula) where
open Structure.Logic.Classical.NaturalDeduction.ClassicalLogic {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} (classicLogic)

open import Functional hiding (Domain)
open import Functional.Instance
import      Lvl
open import Type.Dependent.Sigma
open import Structure.Logic.Classical.PredicateBoundedQuantification {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic ⦄

-- Bounded universal quantifier
∀ₛ : Domain → (Domain → Formula) → Formula
∀ₛ(S)(P) = ∀ₚ(_∈ S)(P)

[∀ₛ]-intro : ∀{S}{P} → (∀{x} → Proof(x ∈ S) → Proof(P(x))) → Proof(∀ₛ(S)(P))
[∀ₛ]-intro = [∀ₚ]-intro

[∀ₛ]-elim : ∀{S}{P} → Proof(∀ₛ(S)(P)) → ∀{x} → Proof(x ∈ S) → Proof(P(x))
[∀ₛ]-elim = [∀ₚ]-elim

-- Bounded existential quantifier
∃ₛ : Domain → (Domain → Formula) → Formula
∃ₛ(S)(P) = ∃ₚ(_∈ S)(P)

[∃ₛ]-intro : ∀{S}{P}{x} → Proof(x ∈ S) → Proof(P(x)) → Proof(∃ₛ(S)(P))
[∃ₛ]-intro = [∃ₚ]-intro

[∃ₛ]-elim : ∀{S}{P}{Q} → (∀{x} → Proof(x ∈ S) → Proof(P(x)) → Proof(Q)) → Proof(∃ₛ(S)(P)) → Proof(Q)
[∃ₛ]-elim = [∃ₚ]-elim

[∃ₛ]-witness : ∀{S : Domain}{P : Domain → Formula} → ⦃ _ : Proof(∃ₛ S P) ⦄ → Domain
[∃ₛ]-witness = [∃ₚ]-witness

[∃ₛ]-domain : ∀{S : Domain}{P : Domain → Formula} → ⦃ p : Proof(∃ₛ S P) ⦄ → Proof([∃ₛ]-witness{S}{P} ⦃ p ⦄ ∈ S)
[∃ₛ]-domain = [∃ₚ]-bound

[∃ₛ]-proof : ∀{S : Domain}{P : Domain → Formula} → ⦃ p : Proof(∃ₛ S P) ⦄ → Proof(P([∃ₛ]-witness{S}{P} ⦃ p ⦄))
[∃ₛ]-proof = [∃ₚ]-proof

Uniqueₛ : Domain → (Domain → Formula) → Formula
Uniqueₛ(S)(P) = Uniqueₚ(_∈ S)(P)

-- Bounded unique existential quantifier
∃ₛ! : Domain → (Domain → Formula) → Formula
∃ₛ!(S)(P) = ∃ₚ!(_∈ S)(P)

[∃ₛ!]-witness : ∀{S : Domain}{P : Domain → Formula} → ⦃ _ : Proof(∃ₛ! S P) ⦄ → Domain
[∃ₛ!]-witness = [∃ₚ!]-witness

[∃ₛ!]-domain : ∀{S : Domain}{P : Domain → Formula} → ⦃ p : Proof(∃ₛ! S P) ⦄ → Proof([∃ₛ!]-witness{S}{P} ⦃ p ⦄ ∈ S)
[∃ₛ!]-domain = [∃ₚ!]-bound

[∃ₛ!]-proof : ∀{S : Domain}{P : Domain → Formula} → ⦃ p : Proof(∃ₛ! S P) ⦄ → Proof(P([∃ₛ!]-witness{S}{P} ⦃ p ⦄))
[∃ₛ!]-proof = [∃ₚ!]-proof

[∃ₛ!]-unique : ∀{S : Domain}{P : Domain → Formula} → ⦃ p : Proof(∃ₛ! S P) ⦄ → Proof(∀ₗ(x ↦ P(x) ⟶ (x ≡ [∃ₛ!]-witness{S}{P} ⦃ p ⦄)))
[∃ₛ!]-unique = [∃ₚ!]-unique
