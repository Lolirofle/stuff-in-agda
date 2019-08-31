module Structure.Operator.SetAlgebra {ℓ₁} {ℓ₂} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
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
  infixl 1002 ∁_
  infixl 1000 _∖_

  field
    ∁_   : S → S -- Complement

  field
    ⦃ fundamentals ⦄ : Fundamentals(S)
  open Fundamentals(fundamentals)

  field
    [∪]-inverseᵣ : ∀{s : S} → (s ∪ ∁(s) ≡ 𝐔)
    [∩]-inverseᵣ : ∀{s : S} → (s ∩ ∁(s) ≡ ∅)

  _∖_ : S → S → S -- Difference
  _∖_ (s₁)(s₂) = s₁ ∩ ∁(s₂)

  [∪]-inverseₗ : ∀{s : S} → (∁(s) ∪ s ≡ 𝐔)
  [∪]-inverseₗ = transitivity [∪]-commutativity [∪]-inverseᵣ

  [∩]-inverseₗ : ∀{s : S} → (∁(s) ∩ s ≡ ∅)
  [∩]-inverseₗ = transitivity [∩]-commutativity [∩]-inverseᵣ

  [∁]-of-[∅] : (∁(∅) ≡ 𝐔)
  [∁]-of-[∅] =
    (symmetry [∪]-identityₗ)
    🝖 ([∪]-inverseᵣ)

  [∁]-of-[𝐔] : (∁(𝐔) ≡ ∅)
  [∁]-of-[𝐔] =
    (symmetry [∩]-identityₗ)
    🝖 ([∩]-inverseᵣ)

  [∪]-idempotence : ∀{s : S} → (s ∪ s) ≡ s
  [∪]-idempotence{s} =
    ([≡]-intro)
    🝖 (symmetry [∩]-identityᵣ)
    🝖 ([≡]-with(expr ↦ ((s ∪ s) ∩ expr)) (symmetry [∪]-inverseᵣ))
    🝖 (symmetry [∪][∩]-distributivityₗ)
    🝖 ([≡]-with(expr ↦ (s ∪ expr)) [∩]-inverseᵣ)
    🝖 ([∪]-identityᵣ)

  [∩]-idempotence : ∀{s : S} → (s ∩ s) ≡ s
  [∩]-idempotence{s} =
    ([≡]-intro)
    🝖 (symmetry [∪]-identityᵣ)
    🝖 ([≡]-with(expr ↦ ((s ∩ s) ∪ expr)) (symmetry [∩]-inverseᵣ))
    🝖 (symmetry [∩][∪]-distributivityₗ)
    🝖 ([≡]-with(expr ↦ (s ∩ expr)) [∪]-inverseᵣ)
    🝖 ([∩]-identityᵣ)

  [∪]-domination : ∀{s : S} → (s ∪ 𝐔) ≡ 𝐔
  [∪]-domination{s} =
    ([≡]-with(expr ↦ s ∪ expr) (symmetry [∪]-inverseᵣ))
    🝖 (symmetry [∪]-associativity)
    🝖 ([≡]-with(expr ↦ expr ∪ ∁(s)) [∪]-idempotence)
    🝖 ([∪]-inverseᵣ)
    -- s∪𝐔 = s∪(s ∪ ∁(s)) = (s∪s) ∪ ∁(s) = s ∪ ∁(s) = 𝐔

  [∩]-domination : ∀{s : S} → (s ∩ ∅) ≡ ∅
  [∩]-domination{s} =
    ([≡]-with(expr ↦ s ∩ expr) (symmetry [∩]-inverseᵣ))
    🝖 (symmetry [∩]-associativity)
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
  [∁∁]-elim {s} = transitivity proof2 (symmetry proof1) where
    proof1 : s ≡ s ∪ ∁(∁(s))
    proof1 =
      [∩]-inverseᵣ {∁(s)}
      ⩺ [≡]-with(s ∪_)
      ⩺ (eq ↦ transitivity eq ([∪]-identityᵣ {s}))
      ⩺ symmetry
      ⩺ (eq ↦ transitivity eq ([∪][∩]-distributivityₗ))
      ⩺ (eq ↦ transitivity eq ([≡]-with(_∩ (s ∪ ∁(∁(s)))) ([∪]-inverseᵣ)))
      ⩺ (eq ↦ transitivity eq ([∩]-identityₗ))
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
      ⩺ (eq ↦ transitivity eq ([∪]-identityₗ))
      ⩺ symmetry
      ⩺ (eq ↦ transitivity eq ([∪][∩]-distributivityᵣ))
      ⩺ (eq ↦ transitivity eq ([≡]-with((s ∪ ∁(∁(s))) ∩_) ([∪]-inverseᵣ)))
      ⩺ (eq ↦ transitivity eq ([∩]-identityᵣ))
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


record Subset (S : Type) : Set(Lvl.𝐒(ℓ₁ Lvl.⊔ ℓ₂)) where
  field
    _⊆_ : S → S → Stmt -- Subset
    ⦃ fundamentals ⦄ : Fundamentals(S)
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
    🝖 [≡]-to-[⊆] [∪]-commutativity

  [⊆]ₗ-of-[∩]ᵣ : ∀{a b} → ((a ∩ b) ⊆ b)
  [⊆]ₗ-of-[∩]ᵣ {a}{b} =
    [≡]-to-[⊆] [∩]-commutativity
    🝖 [⊆]ₗ-of-[∩]ₗ {b}{a}

  [⊆]-min : ∀{s} → (∅ ⊆ s)
  [⊆]-min {s} =
    [⊆]ᵣ-of-[∪]ₗ {∅}{s}
    🝖 [≡]-to-[⊆] [∪]-identityₗ

  [⊆]-max : ∀{s} → (s ⊆ 𝐔)
  [⊆]-max {s} =
    [≡]-to-[⊆] (symmetry [∩]-identityₗ)
    🝖 [⊆]ₗ-of-[∩]ₗ {𝐔}{s}

  [⊆][∩]-equiv : ∀{a b} → (a ⊆ b) ↔ (a ∩ b ≡ a)
  [⊆][∩]-equiv {a}{b} = [↔]-intro l r where
    l : (a ⊆ b) ← (a ∩ b ≡ a)
    l aba =
      [≡]-to-[⊆] (symmetry aba)
      🝖 [⊆]ₗ-of-[∩]ᵣ

    r : (a ⊆ b) → (a ∩ b ≡ a)
    r ab =
      (antisymmetry
        ([⊆]ₗ-of-[∩]ₗ)
        ([⊆]ᵣ-of-[∩] {a}{b}{a} reflexivity ab)
      )
{-
  [⊆][∪]-equiv : ∀{a b} → (a ⊆ b) ↔ (a ∪ b ≡ b)
  [⊆][∪]-equiv {a}{b} = [↔]-intro l r where
    l : (a ⊆ b) ← (a ∪ b ≡ b)
    l aba =
      [≡]-to-[⊆] (symmetry aba)
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
