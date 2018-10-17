open import Structure.Logic.Classical.NaturalDeduction

module Structure.Logic.Classical.SetTheory.BoundedQuantification {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Formula} {Domain} {Proof} ⦃ predicateEqTheory : PredicateEq.Theory{ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Formula} {Domain} (Proof) ⦄ (_∈_ : Domain → Domain → Formula) where

open import Functional hiding (Domain)
open import Lang.Instance
import      Lvl
open        Structure.Logic.Classical.NaturalDeduction.PredicateEq {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Formula} {Domain} (Proof) renaming (Theory to PredicateEqTheory)

open        PredicateEqTheory (predicateEqTheory)

-- Bounded universal quantifier
∀ₛ : Domain → (Domain → Formula) → Formula
∀ₛ(S)(φ) = ∀ₗ(x ↦ (x ∈ S) ⟶ φ(x))

[∀ₛ]-intro : ∀{S}{φ} → (∀{x} → Proof(x ∈ S) → Proof(φ(x))) → Proof(∀ₛ(S)(φ))
[∀ₛ]-intro {S}{φ} proof =
  ([∀]-intro(\{x} →
    ([→]-intro(xinS ↦
      proof{x}(xinS)
    ))
  ))

[∀ₛ]-elim : ∀{S}{φ} → Proof(∀ₛ(S)(φ)) → ∀{x} → Proof(x ∈ S) → Proof(φ(x))
[∀ₛ]-elim {S}{φ} allSφ {x} xinS =
  ([→]-elim
    ([∀]-elim allSφ{x})
    (xinS)
  )

-- Bounded existential quantifier
∃ₛ : Domain → (Domain → Formula) → Formula
∃ₛ(S)(φ) = ∃ₗ(x ↦ (x ∈ S) ∧ φ(x))

[∃ₛ]-intro : ∀{S}{φ}{x} → Proof(x ∈ S) → Proof(φ(x)) → Proof(∃ₛ(S)(φ))
[∃ₛ]-intro {S}{φ}{x} xinS φx =
  ([∃]-intro{_}
    {x}
    ([∧]-intro
      (xinS)
      (φx)
    )
  )

[∃ₛ]-elim : ∀{S}{φ}{ψ} → (∀{x} → Proof(x ∈ S) → Proof(φ(x)) → Proof(ψ)) → Proof(∃ₛ(S)(φ)) → Proof(ψ)
[∃ₛ]-elim {S}{φ}{ψ} proof existence =
  ([∃]-elim{_}{ψ}
    (\{x} → conj ↦ (
      (proof
        {x}
        ([∧]-elimₗ(conj))
        ([∧]-elimᵣ(conj))
      )
    ))
    (existence)
  )

[∃ₛ]-witness : ∀{P : Domain → Formula}{S : Domain} → ⦃ _ : Proof(∃ₛ S P) ⦄ → Domain
[∃ₛ]-witness ⦃ proof ⦄ = [∃]-witness ⦃ proof ⦄

[∃ₛ]-domain : ∀{P : Domain → Formula}{S : Domain} → ⦃ p : Proof(∃ₛ S P) ⦄ → Proof([∃ₛ]-witness{P}{S} ⦃ p ⦄ ∈ S)
[∃ₛ]-domain ⦃ proof ⦄ = [∧]-elimₗ([∃]-proof ⦃ proof ⦄)

[∃ₛ]-proof : ∀{P : Domain → Formula}{S : Domain} → ⦃ p : Proof(∃ₛ S P) ⦄ → Proof(P([∃ₛ]-witness{P}{S} ⦃ p ⦄ ))
[∃ₛ]-proof ⦃ proof ⦄ = [∧]-elimᵣ([∃]-proof ⦃ proof ⦄)

Uniqueₛ : Domain → (Domain → Formula) → Formula
Uniqueₛ(S)(P) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (P(x) ∧ P(y)) ⟶ (x ≡ y)))

-- Bounded unique existential quantifier
∃ₛ! : Domain → (Domain → Formula) → Formula
∃ₛ!(S)(P) = ((∃ₛ(S) P) ∧ Uniqueₛ(S)(P))

[∃ₛ!]-witness : ∀{P : Domain → Formula}{S : Domain} → ⦃ _ : Proof(∃ₛ! S P) ⦄ → Domain
[∃ₛ!]-witness ⦃ proof ⦄ = [∃ₛ]-witness ⦃ [∧]-elimₗ proof ⦄

[∃ₛ!]-domain : ∀{P : Domain → Formula}{S : Domain} → ⦃ p : Proof(∃ₛ! S P) ⦄ → Proof([∃ₛ!]-witness{P}{S} ⦃ p ⦄ ∈ S)
[∃ₛ!]-domain ⦃ proof ⦄ = [∃ₛ]-domain ⦃ [∧]-elimₗ proof ⦄

[∃ₛ!]-proof : ∀{P : Domain → Formula}{S : Domain} → ⦃ p : Proof(∃ₛ! S P) ⦄ → Proof(P([∃ₛ!]-witness{P}{S} ⦃ p ⦄ ))
[∃ₛ!]-proof ⦃ proof ⦄ = [∃ₛ]-proof ⦃ [∧]-elimₗ proof ⦄

postulate [∃ₛ!]-unique  : ∀{P : Domain → Formula}{S : Domain} → ⦃ p : Proof(∃ₛ! S P) ⦄ → Proof(∀ₗ(x ↦ P(x) ⟶ (x ≡ [∃ₛ!]-witness{P}{S} ⦃ p ⦄)))
