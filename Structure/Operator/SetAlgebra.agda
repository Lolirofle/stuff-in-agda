open import Type

module Structure.Operator.SetAlgebra {ℓ} (S : Type{ℓ}) where

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Operator.Properties
open import Structure.Operator.Proofs
open import Structure.Relator.Properties
open import Syntax.Transitivity

record Fundamentals : Stmt{ℓ} where
  infixl 1001 _∩_
  infixl 1000 _∪_

  field
    _∪_ : S → S → S -- Union
    _∩_ : S → S → S -- Intersection
    ∅   : S         -- Empty set
    𝐔   : S         -- Universal set

  field -- TODO: This is two commutative monoids with distributivity over each other
    ⦃ [∪]-commutativity ⦄ : Commutativity(_∪_)
    ⦃ [∩]-commutativity ⦄ : Commutativity(_∩_)

    ⦃ [∪]-associativity ⦄ : Associativity(_∪_)
    ⦃ [∩]-associativity ⦄ : Associativity(_∩_)

    ⦃ [∪][∩]-distributivityₗ ⦄ : Distributivityₗ(_∪_)(_∩_)
    ⦃ [∩][∪]-distributivityₗ ⦄ : Distributivityₗ(_∩_)(_∪_)

    ⦃ [∪]-identityₗ ⦄ : Identityₗ(_∪_)(∅)
    ⦃ [∩]-identityₗ ⦄ : Identityₗ(_∩_)(𝐔)

  instance
    [∪][∩]-distributivityᵣ : Distributivityᵣ(_∪_)(_∩_)
    [∪][∩]-distributivityᵣ = [↔]-to-[→] OneTypeTwoOp.distributivity-equivalence-by-commutativity [∪][∩]-distributivityₗ

  instance
    [∩][∪]-distributivityᵣ : Distributivityᵣ(_∩_)(_∪_)
    [∩][∪]-distributivityᵣ = [↔]-to-[→] OneTypeTwoOp.distributivity-equivalence-by-commutativity [∩][∪]-distributivityₗ

  instance
    [∪]-identityᵣ : Identityᵣ(_∪_)(∅)
    [∪]-identityᵣ = [↔]-to-[→] One.identity-equivalence-by-commutativity [∪]-identityₗ

  instance
    [∩]-identityᵣ : Identityᵣ(_∩_)(𝐔)
    [∩]-identityᵣ = [↔]-to-[→] One.identity-equivalence-by-commutativity [∩]-identityₗ

record Complement : Stmt{ℓ} where
  infixl 1002 ∁_
  infixl 1000 _∖_

  field
    ∁_   : S → S -- Complement

  field
    ⦃ fundamentals ⦄ : Fundamentals
  open Fundamentals(fundamentals)

  field -- TODO: Not really inverses. These are using the absorbers
    [∪]-inverseᵣ : ∀{s : S} → (s ∪ ∁(s) ≡ 𝐔)
    [∩]-inverseᵣ : ∀{s : S} → (s ∩ ∁(s) ≡ ∅)

  _∖_ : S → S → S -- Difference
  _∖_ (s₁)(s₂) = s₁ ∩ ∁(s₂)

  [∪]-inverseₗ : ∀{s : S} → (∁(s) ∪ s ≡ 𝐔)
  [∪]-inverseₗ = transitivity(_≡_) (commutativity(_∪_)) [∪]-inverseᵣ

  [∩]-inverseₗ : ∀{s : S} → (∁(s) ∩ s ≡ ∅)
  [∩]-inverseₗ = transitivity(_≡_) (commutativity(_∩_)) [∩]-inverseᵣ

  [∁]-of-[∅] : (∁(∅) ≡ 𝐔)
  [∁]-of-[∅] =
    symmetry(_≡_) (identityₗ(_∪_)(∅))
    🝖 ([∪]-inverseᵣ)

  [∁]-of-[𝐔] : (∁(𝐔) ≡ ∅)
  [∁]-of-[𝐔] =
    symmetry(_≡_) (identityₗ(_∩_)(𝐔))
    🝖 ([∩]-inverseᵣ)

  [∪]-idempotence : ∀{s : S} → (s ∪ s) ≡ s
  [∪]-idempotence{s} =
    ([≡]-intro)
    🝖 (symmetry(_≡_) (identityᵣ(_∩_)(𝐔)))
    🝖 ([≡]-with(expr ↦ ((s ∪ s) ∩ expr)) (symmetry(_≡_) [∪]-inverseᵣ))
    🝖 (symmetry(_≡_) (distributivityₗ(_∪_)(_∩_)))
    🝖 ([≡]-with(expr ↦ (s ∪ expr)) [∩]-inverseᵣ)
    🝖 ((identityᵣ(_∪_)(∅)))

  [∩]-idempotence : ∀{s : S} → (s ∩ s) ≡ s
  [∩]-idempotence{s} =
    ([≡]-intro)
    🝖 (symmetry(_≡_) (identityᵣ(_∪_)(∅)))
    🝖 ([≡]-with(expr ↦ ((s ∩ s) ∪ expr)) (symmetry(_≡_) [∩]-inverseᵣ))
    🝖 (symmetry(_≡_) (distributivityₗ(_∩_)(_∪_)))
    🝖 ([≡]-with(expr ↦ (s ∩ expr)) [∪]-inverseᵣ)
    🝖 ((identityᵣ(_∩_)(𝐔)))

  [∪]-absorber : ∀{s : S} → (s ∪ 𝐔) ≡ 𝐔
  [∪]-absorber{s} =
    ([≡]-with(expr ↦ s ∪ expr) (symmetry(_≡_) [∪]-inverseᵣ))
    🝖 (symmetry(_≡_) (associativity(_∪_)))
    🝖 ([≡]-with(expr ↦ expr ∪ ∁(s)) [∪]-idempotence)
    🝖 ([∪]-inverseᵣ)
    -- s∪𝐔 = s∪(s ∪ ∁(s)) = (s∪s) ∪ ∁(s) = s ∪ ∁(s) = 𝐔

  [∩]-absorber : ∀{s : S} → (s ∩ ∅) ≡ ∅
  [∩]-absorber{s} =
    ([≡]-with(expr ↦ s ∩ expr) (symmetry(_≡_) [∩]-inverseᵣ))
    🝖 (symmetry(_≡_) (associativity(_∩_)))
    🝖 ([≡]-with(expr ↦ expr ∩ ∁(s)) [∩]-idempotence)
    🝖 ([∩]-inverseᵣ)
    -- s∩∅ = s∩(s ∩ ∁(s)) = (s∩s) ∩ ∁(s) = s ∩ ∁(s) = ∅

  -- postulate [∪]-absorptionₗ : ∀{s₁ s₂ : S} → (s₁ ∪ (s₁ ∩ s₂)) ≡ s₁
    -- s₁∪(s₁∩s₂)
    -- = (s₁∪s₁)∩(s₁∪s₂)
    -- = s₁∩(s₁∪s₂)
    -- = (s₁∩s₁) ∪ (s₁∩s₂)
    -- = s₁ ∪ (s₁∩s₂)
    -- = ?
  -- postulate [∩]-absorptionₗ : ∀{s₁ s₂ : S} → (s₁ ∩ (s₁ ∪ s₂)) ≡ s₁

  -- ∁(s₁) ∪ ∁(s₁ ∪ s₂) = ∁(s₁)
  -- ∁(s₁) ∩ ∁(s₁ ∪ s₂) = ∁(s₁ ∪ s₂)
  -- ∁(s₁) ∪ ∁(s₁ ∩ s₂) = ∁(s₁ ∩ s₂)
  -- ∁(s₁) ∩ ∁(s₁ ∩ s₂) = ∁(s₁)


--    postulate a : ∀{a} → a

  -- postulate [∁]-of-[∪] : ∀{s₁ s₂ : S} → ∁(s₁ ∪ s₂) ≡ ∁(s₁) ∩ ∁(s₂)
  -- [∁]-of-[∪] =
    -- ((∁(s₁) ∩ ∁(s₂)) ∪ (s₁ ∪ s₂)) = 𝐔 ?

    -- (s₁ ∪ s₂) ∪ ∁(s₁ ∪ s₂) = 𝐔
    -- ∁(s₂) ∩ ((s₁ ∪ s₂) ∪ ∁(s₁ ∪ s₂)) = ∁(s₁) ∩ 𝐔
    -- (∁(s₂) ∩ (s₁ ∪ s₂)) ∪ (∁(s₁) ∩ ∁(s₁ ∪ s₂)) = ∁(s₂) ∩ 𝐔
    -- (∁(s₂) ∩ (s₁ ∪ s₂)) ∪ (∁(s₁) ∩ ∁(s₁ ∪ s₂)) = ∁(s₂) ∩ 𝐔
    -- (∁(s₂) ∩ (s₁ ∪ s₂)) ∪ (∁(s₁) ∩ ∁(s₁ ∪ s₂)) = ∁(s₂)
    -- ∁(s₂) = (∁(s₂) ∩ (s₁ ∪ s₂)) ∪ (∁(s₁) ∩ ∁(s₁ ∪ s₂))
    -- ∁(s₂) = ((∁(s₂) ∩ s₁) ∪ (∁(s₂) ∩ s₂)) ∪ ∁(s₁ ∪ s₂)
    -- ∁(s₂) = ((∁(s₂) ∩ s₁) ∪ ∅) ∪ ∁(s₁ ∪ s₂)
    -- ∁(s₂) = (∁(s₂) ∩ s₁) ∪ ∁(s₁ ∪ s₂)
    -- ∁(s₁) ∩ ∁(s₂) = ∁(s₁) ∩ ((∁(s₂) ∩ s₁) ∪ ∁(s₁ ∪ s₂))
    -- ∁(s₁) ∩ ∁(s₂) = (∁(s₁) ∩ (∁(s₂) ∩ s₁)) ∪ (∁(s₁) ∩ ∁(s₁ ∪ s₂))
    -- ∁(s₁) ∩ ∁(s₂) = (∁(s₁) ∩ (∁(s₂) ∩ s₁)) ∪ ∁(s₁ ∪ s₂)
    -- ∁(s₁) ∩ ∁(s₂) = (∁(s₁) ∩ (s₁ ∩ ∁(s₂))) ∪ ∁(s₁ ∪ s₂)
    -- ∁(s₁) ∩ ∁(s₂) = ((∁(s₁) ∩ s₁) ∩ ∁(s₂)) ∪ ∁(s₁ ∪ s₂)
    -- ∁(s₁) ∩ ∁(s₂) = (∅ ∩ ∁(s₂)) ∪ ∁(s₁ ∪ s₂)
    -- ∁(s₁) ∩ ∁(s₂) = ∅ ∪ ∁(s₁ ∪ s₂)
    -- ∁(s₁) ∩ ∁(s₂) = ∁(s₁ ∪ s₂)

    -- postulate proof1 : ∀{a b c d} → (a ∩ b) ∩ (c ∪ d) ≡ (a ∩ (b ∩ d)) ∪ (b ∩ (a ∩ c))
      -- (a ∩ b) ∩ (c ∪ d)
      -- = ((a ∩ b) ∩ c) ∪ ((a ∩ b) ∩ d)
      -- = ((b ∩ a) ∩ c) ∪ ((a ∩ b) ∩ d)
      -- = (b ∩ (a ∩ c)) ∪ ((a ∩ b) ∩ d)
      -- = (b ∩ (a ∩ c)) ∪ (a ∩ (b ∩ d))
      -- = (a ∩ (b ∩ d)) ∪ (b ∩ (a ∩ c))

    -- postulate proof2 : ∀{a b} → (a ∩ b) ∩ (∁(a) ∪ ∁(b)) ≡ ∅
      -- (a ∩ b) ∩ (∁(a) ∪ ∁(b))
      -- = (a ∩ (b ∩ ∁(b))) ∪ (b ∩ (a ∩ ∁(a)))
      -- = (a ∩ ∅) ∪ (b ∩ (a ∩ ∁(a)))
      -- = ∅ ∪ (b ∩ (a ∩ ∁(a)))
      -- = b ∩ (a ∩ ∁(a))
      -- = b ∩ ∅
      -- = ∅

    -- ∁(s₁ ∪ s₂) ∪ (s₁ ∪ s₂) = 𝐔
    -- (∁(s₁ ∪ s₂) ∪ (s₁ ∪ s₂)) ∩ (∁(a) ∪ ∁(b)) = 𝐔 ∩ (∁(a) ∪ ∁(b))
    -- (∁(s₁ ∪ s₂) ∪ (s₁ ∪ s₂)) ∩ (∁(a) ∪ ∁(b)) = ∁(a) ∪ ∁(b)
    -- ∁(a) ∪ ∁(b) = (∁(s₁ ∪ s₂) ∪ (s₁ ∪ s₂)) ∩ (∁(a) ∪ ∁(b))
    -- ∁(a) ∪ ∁(b) = (∁(s₁ ∪ s₂) ∩ (∁(a) ∪ ∁(b))) ∪ ((s₁ ∪ s₂) ∩ (∁(a) ∪ ∁(b)))
    -- ∁(a) ∪ ∁(b) = (∁(s₁ ∪ s₂) ∩ (∁(a) ∪ ∁(b))) ∪ ∅
    -- ∁(a) ∪ ∁(b) = ∁(s₁ ∪ s₂) ∩ (∁(a) ∪ ∁(b))

  postulate [∁]-of-[∩] : ∀{s₁ s₂ : S} → ∁(s₁ ∩ s₂) ≡ ∁(s₁) ∪ ∁(s₂)

  [∁∁]-elim : ∀{s : S} → ∁(∁(s)) ≡ s
  [∁∁]-elim {s} = transitivity(_≡_) proof2 (symmetry(_≡_) proof1) where
    proof1 : s ≡ s ∪ ∁(∁(s))
    proof1 =
      [∩]-inverseᵣ {∁(s)}
      ⩺ [≡]-with(s ∪_)
      ⩺ (eq ↦ transitivity(_≡_) eq ((identityᵣ(_∪_)(∅)) {s}))
      ⩺ symmetry(_≡_)
      ⩺ (eq ↦ transitivity(_≡_) eq ((distributivityₗ(_∪_)(_∩_))))
      ⩺ (eq ↦ transitivity(_≡_) eq ([≡]-with(_∩ (s ∪ ∁(∁(s)))) ([∪]-inverseᵣ)))
      ⩺ (eq ↦ transitivity(_≡_) eq (identityₗ(_∩_)(𝐔)))
      -- ∁(s) ∩ ∁(∁(s)) ≡ ∅
      -- s ∪ (∁(s) ∩ ∁(∁(s))) ≡ s ∪ ∅
      -- s ∪ (∁(s) ∩ ∁(∁(s))) ≡ s
      -- s ≡ s ∪ (∁(s) ∩ ∁(∁(s)))
      -- s ≡ (s ∪ ∁(s)) ∩ (s ∪ ∁(∁(s)))
      -- s ≡ 𝐔 ∩ (s ∪ ∁(∁(s)))
      -- s ≡ s ∪ ∁(∁(s))

    proof2 : ∁(∁(s)) ≡ s ∪ ∁(∁(s))
    proof2 =
      [∩]-inverseᵣ {s}
      ⩺ [≡]-with(_∪ ∁(∁(s)))
      ⩺ (eq ↦ transitivity(_≡_) eq (identityₗ(_∪_)(∅)))
      ⩺ symmetry(_≡_)
      ⩺ (eq ↦ transitivity(_≡_) eq ((distributivityᵣ(_∪_)(_∩_))))
      ⩺ (eq ↦ transitivity(_≡_) eq ([≡]-with((s ∪ ∁(∁(s))) ∩_) ([∪]-inverseᵣ)))
      ⩺ (eq ↦ transitivity(_≡_) eq ((identityᵣ(_∩_)(𝐔))))
      -- (s ∩ ∁(s)) ∪ ∁(∁(s)) ≡ ∅ ∪ ∁(∁(s))
      -- (s ∩ ∁(s)) ∪ ∁(∁(s)) ≡ ∁(∁(s))
      -- ∁(∁(s)) ≡ (s ∩ ∁(s)) ∪ ∁(∁(s))
      -- ∁(∁(s)) ≡ (s ∪ ∁(∁(s))) ∩ (∁(s) ∪ ∁(∁(s)))
      -- ∁(∁(s)) ≡ (s ∪ ∁(∁(s))) ∩ 𝐔
      -- ∁(∁(s)) ≡ s ∪ ∁(∁(s))

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


record Subset : Type{Lvl.𝐒(ℓ)} where
  field
    _⊆_ : S → S → Stmt{ℓ} -- Subset
    ⦃ fundamentals ⦄ : Fundamentals
  open Fundamentals(fundamentals)

  field
    ⦃ [⊆]-antisymmetry ⦄ : Antisymmetry(_⊆_)(_≡_)
    ⦃ [⊆]-transitivity ⦄ : Transitivity(_⊆_)
    ⦃ [⊆]-reflexivity  ⦄ : Reflexivity(_⊆_)

    [≡]-to-[⊆] : ∀{a b} → (a ≡ b) → (a ⊆ b)

    [⊆]ₗ-of-[∪] : ∀{a b c} → (a ⊆ c) → (b ⊆ c) → ((a ∪ b) ⊆ c)
    [⊆]ᵣ-of-[∪]ₗ : ∀{a b} → (a ⊆ (a ∪ b))

    [⊆]ₗ-of-[∩]ₗ : ∀{a b} → ((a ∩ b) ⊆ a)
    [⊆]ᵣ-of-[∩] : ∀{a b c} → (c ⊆ a) → (c ⊆ b) → (c ⊆ (a ∩ b))

  [⊆]ᵣ-of-[∪]ᵣ : ∀{a b} → (b ⊆ (a ∪ b))
  [⊆]ᵣ-of-[∪]ᵣ {a}{b} =
    [⊆]ᵣ-of-[∪]ₗ {b}{a}
    🝖 [≡]-to-[⊆] (commutativity(_∪_))

  [⊆]ₗ-of-[∩]ᵣ : ∀{a b} → ((a ∩ b) ⊆ b)
  [⊆]ₗ-of-[∩]ᵣ {a}{b} =
    [≡]-to-[⊆] (commutativity(_∩_))
    🝖 [⊆]ₗ-of-[∩]ₗ {b}{a}

  [⊆]-min : ∀{s} → (∅ ⊆ s)
  [⊆]-min {s} =
    [⊆]ᵣ-of-[∪]ₗ {∅}{s}
    🝖 [≡]-to-[⊆] (identityₗ(_∪_)(∅))

  [⊆]-max : ∀{s} → (s ⊆ 𝐔)
  [⊆]-max {s} =
    [≡]-to-[⊆] (symmetry(_≡_) (identityₗ(_∩_)(𝐔)))
    🝖 [⊆]ₗ-of-[∩]ₗ {𝐔}{s}

  [⊆][∩]-equiv : ∀{a b} → (a ⊆ b) ↔ (a ∩ b ≡ a)
  [⊆][∩]-equiv {a}{b} = [↔]-intro l r where
    l : (a ⊆ b) ← (a ∩ b ≡ a)
    l aba =
      [≡]-to-[⊆] (symmetry(_≡_) aba)
      🝖 [⊆]ₗ-of-[∩]ᵣ

    r : (a ⊆ b) → (a ∩ b ≡ a)
    r ab =
      (antisymmetry(_⊆_)(_≡_)
        ([⊆]ₗ-of-[∩]ₗ)
        ([⊆]ᵣ-of-[∩] {a}{b}{a} (reflexivity(_⊆_)) ab)
      )
{-
  [⊆][∪]-equiv : ∀{a b} → (a ⊆ b) ↔ (a ∪ b ≡ b)
  [⊆][∪]-equiv {a}{b} = [↔]-intro l r where
    l : (a ⊆ b) ← (a ∪ b ≡ b)
    l aba =
      [≡]-to-[⊆] (symmetry(_≡_) aba)
      🝖 [⊆]ᵣ-of-[∪]ᵣ

    r : (a ⊆ b) → (a ∪ b ≡ b)
    r ab =
      (antisymmetry
        ([⊆]ᵣ-of-[∪]ᵣ)
        ([⊆]ₗ-of-[∪] {a}{b}{a} reflexivity ab)
      )
-}
  -- [⊆][∖]-equiv : (a ⊆ b) ↔ (a ∖ b ≡ ∅)

  -- [⊆][∁]-equiv : (a ⊆ b) ↔ (∁(b) ⊆ ∁(a))

  -- [∩][∪]-sub : (a ∩ b) ⊆ (a ∪ b)
