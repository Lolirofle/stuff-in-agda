open import Logic.Classical.NaturalDeduction

module Logic.Classical.SetTheory.BoundedQuantification {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} {Proof} ⦃ predicateEqTheory : PredicateEq.Theory{ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} (Proof) ⦄ (_∈_ : Domain → Domain → Stmt) where

open import Functional hiding (Domain)
open import Lang.Instance
import      Lvl
open        Logic.Classical.NaturalDeduction.PredicateEq {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} (Proof) renaming (Theory to PredicateEqTheory)

open        PredicateEqTheory (predicateEqTheory)

-- Bounded universal quantifier
∀ₛ : Domain → (Domain → Stmt) → Stmt
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
∃ₛ : Domain → (Domain → Stmt) → Stmt
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

-- Bounded unique existential quantifier
∃ₛ! : Domain → (Domain → Stmt) → Stmt
∃ₛ!(S)(φ) = ∃ₗ!(x ↦ (x ∈ S) ∧ φ(x))
