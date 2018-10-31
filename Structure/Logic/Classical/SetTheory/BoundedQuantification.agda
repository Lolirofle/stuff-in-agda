import Structure.Logic.Classical.NaturalDeduction

-- TODO: MAybe rename to SetBoundedQuantification
module Structure.Logic.Classical.SetTheory.BoundedQuantification {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} {ℓₘₒ} {Object} {obj} ⦃ sign : _ ⦄ ⦃ theory : _ ⦄ (_∈_ : Domain → Domain → Formula) where
private module PredicateEq = Structure.Logic.Classical.NaturalDeduction.PredicateEq {ℓₗ} {Formula} {ℓₘₗ} (Proof) {ℓₒ} (Domain) {ℓₘₒ} {Object} (obj)
open PredicateEq.Signature(sign)
open PredicateEq.Theory(theory)

open import Functional hiding (Domain)
open import Lang.Instance
import      Lvl
open import Type.Dependent
open import Structure.Logic.Classical.BoundedQuantification {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} {ℓₘₒ} {Object} {obj} ⦃ sign ⦄ ⦃ theory ⦄

-- Bounded universal quantifier
∀ₛ : Domain → (Domain → Formula) → Formula
∀ₛ(S)(P) = ∀ₚ(_∈ S)(P)

[∀ₛ]-intro : ∀{S}{P} → (∀{x} → Proof((obj x) ∈ S) → Proof(P(obj x))) → Proof(∀ₛ(S)(P))
[∀ₛ]-intro = [∀ₚ]-intro

[∀ₛ]-elim : ∀{S}{P} → Proof(∀ₛ(S)(P)) → ∀{x} → Proof((obj x) ∈ S) → Proof(P(obj x))
[∀ₛ]-elim = [∀ₚ]-elim

-- Bounded existential quantifier
∃ₛ : Domain → (Domain → Formula) → Formula
∃ₛ(S)(P) = ∃ₚ(_∈ S)(P)

[∃ₛ]-intro : ∀{S}{P}{x} → Proof((obj x) ∈ S) → Proof(P(obj x)) → Proof(∃ₛ(S)(P))
[∃ₛ]-intro = [∃ₚ]-intro

[∃ₛ]-elim : ∀{S}{P}{Q} → (∀{x} → Proof((obj x) ∈ S) → Proof(P(obj x)) → Proof(Q)) → Proof(∃ₛ(S)(P)) → Proof(Q)
[∃ₛ]-elim = [∃ₚ]-elim

[∃ₛ]-witness : ∀{S : Domain}{P : Domain → Formula} → ⦃ _ : Proof(∃ₛ S P) ⦄ → Object
[∃ₛ]-witness = [∃ₚ]-witness

[∃ₛ]-domain : ∀{S : Domain}{P : Domain → Formula} → ⦃ p : Proof(∃ₛ S P) ⦄ → Proof(obj([∃ₛ]-witness{S}{P} ⦃ p ⦄) ∈ S)
[∃ₛ]-domain = [∃ₚ]-bound

[∃ₛ]-proof : ∀{S : Domain}{P : Domain → Formula} → ⦃ p : Proof(∃ₛ S P) ⦄ → Proof(P(obj([∃ₛ]-witness{S}{P} ⦃ p ⦄)))
[∃ₛ]-proof = [∃ₚ]-proof

Uniqueₛ : Domain → (Domain → Formula) → Formula
Uniqueₛ(S)(P) = Uniqueₚ(_∈ S)(P)

-- Bounded unique existential quantifier
∃ₛ! : Domain → (Domain → Formula) → Formula
∃ₛ!(S)(P) = ∃ₚ!(_∈ S)(P)

[∃ₛ!]-witness : ∀{S : Domain}{P : Domain → Formula} → ⦃ _ : Proof(∃ₛ! S P) ⦄ → Object
[∃ₛ!]-witness = [∃ₚ!]-witness

[∃ₛ!]-domain : ∀{S : Domain}{P : Domain → Formula} → ⦃ p : Proof(∃ₛ! S P) ⦄ → Proof(obj([∃ₛ!]-witness{S}{P} ⦃ p ⦄) ∈ S)
[∃ₛ!]-domain = [∃ₚ!]-bound

[∃ₛ!]-proof : ∀{S : Domain}{P : Domain → Formula} → ⦃ p : Proof(∃ₛ! S P) ⦄ → Proof(P(obj([∃ₛ!]-witness{S}{P} ⦃ p ⦄)))
[∃ₛ!]-proof = [∃ₚ!]-proof

[∃ₛ!]-unique : ∀{S : Domain}{P : Domain → Formula} → ⦃ p : Proof(∃ₛ! S P) ⦄ → Proof(∀ₗ(x ↦ P(x) ⟶ (x ≡ obj([∃ₛ!]-witness{S}{P} ⦃ p ⦄))))
[∃ₛ!]-unique = [∃ₚ!]-unique
