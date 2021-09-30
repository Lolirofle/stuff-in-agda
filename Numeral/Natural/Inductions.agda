module Numeral.Natural.Inductions where

import Lvl
open import Logic
open import Logic.Propositional
open import Functional
open import Numeral.Natural
open import Numeral.Natural.Induction
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Type

private variable ℓ : Lvl.Level

ℕ-strong-recursion : (P : ℕ → Type{ℓ}) → ((n : ℕ) → ((i : ℕ) → (i < n) → P(i)) → P(n)) → ((n : ℕ) → P(n))
ℕ-strong-recursion P step n = ℕ-elim{T = n ↦ ((i : ℕ) → (i < n) → P(i))}
  (\_ ())
  (n ↦ prev ↦ i ↦ i𝐒n ↦ step i (j ↦ ji ↦ prev j (transitivity(_≤_) ji ([≤]-without-[𝐒] i𝐒n))))
  (𝐒(n)) n (reflexivity(_≤_))

ℕ-split-strong-recursion : (P : ℕ → Type{ℓ}) → (s : ℕ) → ((i : ℕ) → (i ≤ s) → P(i)) → ((n : ℕ) → ((i : ℕ) → (s < i < n) → P(i)) → P(n)) → ((n : ℕ) → P(n))
ℕ-split-strong-recursion P s base step = ℕ-strong-recursion P (n ↦ prev ↦ step n (i ↦ prev i ∘ [∧]-elimᵣ))

ℕ-strong-induction : ∀{φ : ℕ → Stmt{ℓ}} → φ(𝟎) → (∀{i : ℕ} → (∀{j : ℕ} → (j ≤ i) → φ(j)) → φ(𝐒(i))) → (∀{n} → φ(n))
ℕ-strong-induction {φ = φ} base step {n} = ℕ-strong-recursion φ (\{𝟎 _ → base ; (𝐒(n)) prev → step{n} (\{i} → prev i ∘ succ)}) n

module _ where
  open Strict.Properties

  instance
    ℕ-accessibleₗ : ∀{n} → Accessibleₗ(_<_)(n)
    ℕ-accessibleₗ{n} = intro ⦃ proof{n} ⦄ where
      proof : ∀{n m} → ⦃ _ : (m < n) ⦄ → Accessibleₗ(_<_)(m)
      proof {𝟎}   {m}    ⦃ ⦄
      proof{𝐒(n)} {𝟎}    ⦃ succ mn ⦄ = intro ⦃ \ ⦃ ⦄ ⦄
      proof{𝐒(n)} {𝐒(m)} ⦃ succ mn ⦄ = intro ⦃ \{k} ⦃ xsm ⦄ → Accessibleₗ.proof (ℕ-accessibleₗ {n}) ⦃ transitivity(_≤_) xsm mn ⦄ ⦄

  ℕ-wellfounded : WellFounded(_<_)
  ℕ-wellfounded = ℕ-accessibleₗ
