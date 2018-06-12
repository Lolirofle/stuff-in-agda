module Structure.Operator.SetAlgebra {ℓ₁} {ℓ₂} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂}{ℓ₂}
open import Relator.Equals.Proofs{ℓ₁}{ℓ₂}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Structure.Relator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

record Fundamentals (S : Type) : Stmt where
  infixl 1001 _∩_
  infixl 1000 _∪_

  field
    _∪_ : S → S → S -- Union
    _∩_ : S → S → S -- Intersection
    ∅   : S         -- Empty set
    𝐔   : S         -- Universal set

  field
    [∪]-commutativity : Commutativity{S}(_∪_)
    [∩]-commutativity : Commutativity{S}(_∩_)

    [∪]-associativity : Associativity{S}(_∪_)
    [∩]-associativity : Associativity{S}(_∩_)

    [∪][∩]-distributivityₗ : Distributivityₗ{S}(_∪_)(_∩_)
    [∩][∪]-distributivityₗ : Distributivityₗ{S}(_∩_)(_∪_)

    [∪]-identityₗ : Identityₗ{S}(_∪_)(∅)
    [∩]-identityₗ : Identityₗ{S}(_∩_)(𝐔)

  -- TODO: Theorems from https://en.wikipedia.org/wiki/Algebra_of_sets
  [∪][∩]-distributivityᵣ : Distributivityᵣ{S}(_∪_)(_∩_)
  [∪][∩]-distributivityᵣ{a}{b}{c} =
    [∪]-commutativity
    🝖 [∪][∩]-distributivityₗ
    🝖 ([≡]-with(expr ↦ (expr ∩ (c ∪ b))) [∪]-commutativity)
    🝖 ([≡]-with(expr ↦ ((a ∪ c) ∩ expr)) [∪]-commutativity)

  [∩][∪]-distributivityᵣ : Distributivityᵣ{S}(_∩_)(_∪_)
  [∩][∪]-distributivityᵣ{a}{b}{c} =
    [∩]-commutativity
    🝖 [∩][∪]-distributivityₗ
    🝖 ([≡]-with(expr ↦ (expr ∪ (c ∩ b))) [∩]-commutativity)
    🝖 ([≡]-with(expr ↦ ((a ∩ c) ∪ expr)) [∩]-commutativity)

  [∪]-identityᵣ : Identityᵣ{S}(_∪_)(∅)
  [∪]-identityᵣ =
    ([∪]-commutativity)
    🝖 ([∪]-identityₗ)

  [∩]-identityᵣ : Identityᵣ{S}(_∩_)(𝐔)
  [∩]-identityᵣ =
    ([∩]-commutativity)
    🝖 ([∩]-identityₗ)

record Complement (S : Type) : Stmt where
  open Fundamentals ⦃ ... ⦄

  infixl 1002 ∁_
  infixl 1000 _∖_

  field
    ∁_   : S → S -- Complement

  field
    ⦃ fundamentals ⦄ : Fundamentals(S)
    [∪]-with-[∁] : ∀{s : S} → (s ∪ ∁(s) ≡ 𝐔)
    [∩]-with-[∁] : ∀{s : S} → (s ∩ ∁(s) ≡ ∅)

  _∖_ : S → S → S -- Difference
  _∖_ (s₁)(s₂) = s₁ ∩ ∁(s₂)

  [∁]-of-[∅] : (∁(∅) ≡ 𝐔)
  [∁]-of-[∅] =
    (symmetry [∪]-identityₗ)
    🝖 ([∪]-with-[∁])

  [∁]-of-[𝐔] : (∁(𝐔) ≡ ∅)
  [∁]-of-[𝐔] =
    (symmetry [∩]-identityₗ)
    🝖 ([∩]-with-[∁])

  [∪]-idempotence : ∀{s : S} → (s ∪ s) ≡ s
  [∪]-idempotence{s} =
    ([≡]-intro)
    🝖 (symmetry [∩]-identityᵣ)
    🝖 ([≡]-with(expr ↦ ((s ∪ s) ∩ expr)) (symmetry [∪]-with-[∁]))
    🝖 (symmetry [∪][∩]-distributivityₗ)
    🝖 ([≡]-with(expr ↦ (s ∪ expr)) [∩]-with-[∁])
    🝖 ([∪]-identityᵣ)

  [∩]-idempotence : ∀{s : S} → (s ∩ s) ≡ s
  [∩]-idempotence{s} =
    ([≡]-intro)
    🝖 (symmetry [∪]-identityᵣ)
    🝖 ([≡]-with(expr ↦ ((s ∩ s) ∪ expr)) (symmetry [∩]-with-[∁]))
    🝖 (symmetry [∩][∪]-distributivityₗ)
    🝖 ([≡]-with(expr ↦ (s ∩ expr)) [∪]-with-[∁])
    🝖 ([∩]-identityᵣ)

  [∪]-domination : ∀{s : S} → (s ∪ 𝐔) ≡ 𝐔
  [∪]-domination{s} =
    ([≡]-with(expr ↦ s ∪ expr) (symmetry [∪]-with-[∁]))
    🝖 (symmetry [∪]-associativity)
    🝖 ([≡]-with(expr ↦ expr ∪ ∁(s)) [∪]-idempotence)
    🝖 ([∪]-with-[∁])
    -- s∪𝐔 = s∪(s ∪ ∁(s)) = (s∪s) ∪ ∁(s) = s ∪ ∁(s) = 𝐔

  [∩]-domination : ∀{s : S} → (s ∩ ∅) ≡ ∅
  [∩]-domination{s} =
    ([≡]-with(expr ↦ s ∩ expr) (symmetry [∩]-with-[∁]))
    🝖 (symmetry [∩]-associativity)
    🝖 ([≡]-with(expr ↦ expr ∩ ∁(s)) [∩]-idempotence)
    🝖 ([∩]-with-[∁])
    -- s∩∅ = s∩(s ∩ ∁(s)) = (s∩s) ∩ ∁(s) = s ∩ ∁(s) = ∅

  postulate [∪]-absorptionₗ : ∀{s₁ s₂ : S} → (s₁ ∪ (s₁ ∩ s₂)) ≡ s₁
    -- s₁∪(s₁∩s₂)
    -- = (s₁∪s₁)∩(s₁∪s₂)
    -- = s₁∩(s₁∪s₂)
    -- = ?
  postulate [∩]-absorptionₗ : ∀{s₁ s₂ : S} → (s₁ ∩ (s₁ ∪ s₂)) ≡ s₁

  postulate [∁]-of-[∪] : ∀{s₁ s₂ : S} → ∁(s₁ ∪ s₂) ≡ ∁(s₁) ∩ ∁(s₂)
  postulate [∁]-of-[∩] : ∀{s₁ s₂ : S} → ∁(s₁ ∩ s₂) ≡ ∁(s₁) ∪ ∁(s₂)
  postulate [∁∁] : ∀{s : S} → ∁(∁(s)) ≡ s
  postulate [∁]-uniqueness : ∀{s₁ s₂ : S} → (s₁ ∪ s₂ ≡ 𝐔) → (s₁ ∩ s₂ ≡ ∅) → (s₁ ≡ ∁(s₂))

  postulate [∁]-of-[∖] : ∀{s₁ s₂ : S} → ∁(s₁ ∖ s₂) ≡ ∁(s₁) ∪ s₂
  postulate [∖]-of-[∁] : ∀{s₁ s₂ : S} → ∁(s₁) ∖ ∁(s₂) ≡ s₂ ∖ s₁

  postulate [∖]-of-[∪]ᵣ : ∀{s₁ s₂ s₃ : S} → (s₁ ∖ (s₂ ∪ s₃)) ≡ (s₁ ∖ s₂)∩(s₁ ∖ s₃)
  postulate [∖]-of-[∩]ᵣ : ∀{s₁ s₂ s₃ : S} → (s₁ ∖ (s₂ ∩ s₃)) ≡ (s₁ ∖ s₂)∪(s₁ ∖ s₃)

  postulate [∖]-of-[∖]ᵣ : ∀{s₁ s₂ s₃ : S} → (s₁ ∖ (s₂ ∖ s₃)) ≡ (s₁ ∩ s₃)∪(s₁ ∖ s₂)
  postulate [∩]-from-[∖] : ∀{s₁ s₂ : S} → (s₁ ∖ (s₁ ∖ s₂)) ≡ (s₁ ∩ s₂) -- TODO: from [∖]-of-[∖]ᵣ

  postulate [∖]-self : ∀{s : S} → s ∖ s ≡ ∅
  postulate [∖]-of-[∅]ₗ : ∀{s : S} → ∅ ∖ s ≡ ∅
  postulate [∖]-of-[∅]ᵣ : ∀{s : S} → s ∖ ∅ ≡ s
  postulate [∖]-of-[𝐔]ₗ : ∀{s : S} → 𝐔 ∖ s ≡ ∁(s)
  postulate [∖]-of-[𝐔]ᵣ : ∀{s : S} → s ∖ 𝐔 ≡ ∅
