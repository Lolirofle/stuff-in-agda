module Numeral.Natural.Inductions where

import Lvl
open import Logic
open import Logic.Propositional
open import Functional
open import DependentFunctional using () renaming (const to constDep)
open import Numeral.Natural
open import Numeral.Natural.Induction
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Type

private variable ℓ : Lvl.Level

module _
  (P : ℕ → Type{ℓ})
  (step : (n : ℕ) → ((i : ℕ) → (i < n) → P(i)) → P(n))
  where

  ℕ-strong-recursion-internals : (n : ℕ) → (i : ℕ) → (i < n) → P(i)
  ℕ-strong-recursion-internals = ℕ-elim(n ↦ ((i : ℕ) → (i < n) → P(i)))
    (constDep([⊥]-elim ∘ [≤][0]ᵣ-negation))
    (n ↦ prev ↦ i ↦ i𝐒n ↦ step i (j ↦ ji ↦ prev j (transitivity(_≤_) ji ([≤]-without-[𝐒] i𝐒n))))

  ℕ-strong-recursion : (n : ℕ) → P(n)
  ℕ-strong-recursion n = ℕ-strong-recursion-internals (𝐒(n)) n (reflexivity(_≤_))

{-
module _
  (P : ℕ → Type{ℓ})
  (s : ℕ)
  -- (base : (i : ℕ) → (i ≤ s) → P(i))
  (step : (n : ℕ) → ((i : ℕ) → (s < i < n) → P(i)) → P(n))
  where

  ℕ-split-strong-recursion : (n : ℕ) → P(n)
  ℕ-split-strong-recursion = ℕ-strong-recursion P (n ↦ prev ↦ step n (i ↦ prev i ∘ [∧]-elimᵣ))
-}

module _
  (P : ℕ → Type{ℓ})
  (base : P(𝟎))
  (step : ∀(n : ℕ) → ((i : ℕ) → (i ≤ n) → P(i)) → P(𝐒(n)))
  where

  ℕ-strong-induction : (n : ℕ) → P(n)
  ℕ-strong-induction = ℕ-strong-recursion(P) (\{𝟎 _ → base ; (𝐒(n)) prev → step n (\i → prev i ∘ succ)})

module _ where
  open Strict.Properties

  instance
    ℕ-wellfounded : WellFounded(_<_)
    ℕ-wellfounded{n} = intro ⦃ proof{n} ⦄ where
      proof : ∀{n m} → ⦃ _ : (m < n) ⦄ → Accessibleₗ(_<_)(m)
      proof {𝟎}   {m}    ⦃ ⦄
      proof{𝐒(n)} {𝟎}    ⦃ succ mn ⦄ = intro ⦃ \ ⦃ ⦄ ⦄
      proof{𝐒(n)} {𝐒(m)} ⦃ succ mn ⦄ = intro ⦃ \{k} ⦃ xsm ⦄ → Accessibleₗ.proof (ℕ-wellfounded {n}) ⦃ transitivity(_≤_) xsm mn ⦄ ⦄

