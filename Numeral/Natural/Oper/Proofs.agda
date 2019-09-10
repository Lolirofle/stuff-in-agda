module Numeral.Natural.Oper.Proofs where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
import      Functional.Names as Names
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Induction
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Numeral.Natural.Relation.Order.Classical
open import Relator.Equals
open import Relator.Equals.Proofs
open import Sets.Setoid.Uniqueness
open import Structure.Function.Domain
open import Structure.Operator.Properties
import      Structure.Operator.Names as Names
open import Structure.Relator.Properties

[+]-identityₗ-raw : Names.Identityₗ (_+_) (0)
[+]-identityₗ-raw {x} = [ℕ]-induction base next {x} where
  base : ((0 + 0) ≡ 0)
  base = [≡]-intro

  next : ∀(i : ℕ) → ((0 + i) ≡ i) → ((0 + 𝐒(i)) ≡ 𝐒(i))
  next _ = [≡]-with(𝐒)
{-# REWRITE [+]-identityₗ-raw #-}

[+]-identityᵣ-raw : Names.Identityᵣ (_+_) (0)
[+]-identityᵣ-raw {x} = [ℕ]-induction base next {x} where
  base : ((0 + 0) ≡ 0)
  base = [≡]-intro

  next : ∀(i : ℕ) → ((i + 0) ≡ i) → ((𝐒(i) + 0) ≡ 𝐒(i))
  next _ = [≡]-with(𝐒)

[+]-associativity-raw : Names.Associativity (_+_)
[+]-associativity-raw {x}{y}{z} = [ℕ]-induction (base x y) (next x y) {z} where
  base : (x y : ℕ) → ((x + y) + 0) ≡ (x + (y + 0))
  base _ _ = [≡]-intro

  next : ∀(x y i : ℕ) → ((x + y) + i) ≡ (x + (y + i)) → ((x + y) + 𝐒(i)) ≡ (x + (y + 𝐒(i)))
  next _ _ _ = [≡]-with(𝐒)
{-# REWRITE [+]-associativity-raw #-}

[+1]-commutativity : ∀{x y : ℕ} → (𝐒(x) + y) ≡ (x + 𝐒(y))
[+1]-commutativity {x}{y} = [ℕ]-induction (base x) (next x) {y} where
  base : (x : ℕ) → (𝐒(x) + 0) ≡ (x + 𝐒(0))
  base _ = [≡]-intro

  next : ∀(x i : ℕ) → (𝐒(x) + i) ≡ (x + 𝐒(i)) → (𝐒(x) + 𝐒(i)) ≡ (x + 𝐒(𝐒(i)))
  next(x)(_) = [≡]-with(𝐒)
{-# REWRITE [+1]-commutativity #-}

[+]-commutativity-raw : Names.Commutativity (_+_)
[+]-commutativity-raw {x}{y} = [ℕ]-induction (base x) (next x) {y} where
  base : ∀(x : ℕ) → (x + 0) ≡ (0 + x)
  base _ =
    symmetry(_≡_)(
      [+]-identityₗ-raw
      🝖 (symmetry(_≡_) [+]-identityᵣ-raw)
    )
  -- (∀x. 0+x = x) ∧ (∀x. x = x+0) // [∧]-intro [1] [2]
  --   ∀x. 0+x = x //[+]-identityₗ [1]

  --   ∀x. x+0 = x //[+]-identityᵣ
  --   ∀x. x = x+0 //[≡]-symmetry(..) [2]
  -- (∀x. 0+x = x+0) // [≡]-transitivity(..)

  next : ∀(x i : ℕ) → ((x + i) ≡ (i + x)) → ((x + 𝐒(i)) ≡ (𝐒(i) + x))
  next (x) (i) (eq) =
    ([≡]-with(𝐒) eq)
    🝖 (symmetry(_≡_)([+1]-commutativity {i} {x}))
  --   ∀x∀i. x+i = i+x //eq
  --   ∀x∀i. 𝐒(x+i) = 𝐒(i+x) //[≡]-with(𝐒)(..)
  --   ∀x∀i. x+𝐒(i) = i+𝐒(x) //x + 𝐒(y) = 𝐒(x + y) (Definition of _+_) [1]

  --   ∀x∀i. 𝐒(i)+x = i+𝐒(x) //[+1]-commutativity
  --   ∀x∀i. i+𝐒(x) = 𝐒(i)+x //[≡]-symmetry [2]
  -- ∀x∀i. x+𝐒(i) = 𝐒(i)+x //[≡]-transitivity [1] [2]

[+1]-and-[𝐒] : ∀{x : ℕ} → (x + 1 ≡ 𝐒(x))
[+1]-and-[𝐒] {x} = [≡]-intro

[1+]-and-[𝐒] : ∀{x : ℕ} → (1 + x ≡ 𝐒(x))
[1+]-and-[𝐒] {x} = ([+1]-and-[𝐒] {x}) 🝖 ([+]-commutativity-raw{x}{1})

[⋅]-absorberₗ-raw : Names.Absorberₗ (_⋅_) (0)
[⋅]-absorberₗ-raw {x} = [ℕ]-induction base next {x} where
  base : (0 ⋅ 0) ≡ 0
  base = reflexivity(_≡_)

  next : ∀(x : ℕ) → ((0 ⋅ x) ≡ 0) → ((0 ⋅ 𝐒(x)) ≡ 0)
  next(_)(eq) = [≡]-with(x ↦ 0 + x) eq
{-# REWRITE [⋅]-absorberₗ-raw #-}

[⋅]-absorberᵣ-raw : Names.Absorberᵣ (_⋅_) (0)
[⋅]-absorberᵣ-raw = [≡]-intro

[⋅]-identityₗ-raw : Names.Identityₗ (_⋅_) (1)
[⋅]-identityₗ-raw {x} = [ℕ]-induction base next {x} where
  base : ((1 ⋅ 0) ≡ 0)
  base = reflexivity(_≡_)

  next : ∀(i : ℕ) → ((1 ⋅ i) ≡ i) → ((1 ⋅ 𝐒(i)) ≡ 𝐒(i))
  next(i)(eq) =
    ([+]-commutativity-raw {1} {1 ⋅ i})
    🝖 ([≡]-with(𝐒) eq)
--   1 + 1⋅i = 1⋅i + 1 //[+]-commutativity

--   1⋅i = i //eq
--   𝐒(1⋅i) = 𝐒(i) //[≡]-with[ 𝐒 ] (..)
--   1⋅i + 1 = 𝐒(i) //Definition: (+)
-- 1 + 1⋅i = 𝐒(i)
-- 1 ⋅ 𝐒(i) = 𝐒(i) //1 ⋅ 𝐒(y) = 1 + (1 ⋅ y) (Definition: (⋅))
{-# REWRITE [⋅]-identityₗ-raw #-}

[⋅]-identityᵣ-raw : Names.Identityᵣ (_⋅_) (1)
[⋅]-identityᵣ-raw = [≡]-intro

[⋅][+]-distributivityᵣ-raw : Names.Distributivityᵣ(_⋅_)(_+_)
[⋅][+]-distributivityᵣ-raw {x}{y}{z} = [ℕ]-induction (base x y) (next x y) {z} where
  base : (x y : ℕ) → ((x + y) ⋅ 0) ≡ ((x ⋅ 0) + (y ⋅ 0))
  base _ _ = [≡]-intro

  next : ∀(x y z : ℕ) → ((x + y) ⋅ z) ≡ ((x ⋅ z) + (y ⋅ z)) → ((x + y) ⋅ 𝐒(z)) ≡ ((x ⋅ 𝐒(z)) + (y ⋅ 𝐒(z)))
  next(x)(y)(z) (proof) = ([≡]-with(expr ↦ ((x + y) + expr)) proof) 🝖 (swap-stuff-around{x}{y}{x ⋅ z}{y ⋅ z}) where
    swap-stuff-around : ∀{a b c d} → (a + b) + (c + d) ≡ (a + c) + (b + d)
    swap-stuff-around {a}{b}{c}{d} =
      [+]-associativity-raw{a}{b}{c + d}
      🝖 ([≡]-with(expr ↦ a + expr) ([+]-commutativity-raw{b}{c + d}))
      🝖 ([≡]-with(expr ↦ a + expr) ([+]-associativity-raw{c}{d}{b}))
      🝖 ([≡]-with(expr ↦ a + (c + expr)) ([+]-commutativity-raw{d}{b}))
      🝖 (symmetry(_≡_)([+]-associativity-raw{a}{c}{b + d}))
  -- (x+y)⋅𝐒(z)
  -- = (x+y) + (x+y)⋅z //Definition: (⋅)
  -- = (x+y) + (x⋅z + y⋅z) //proof
  -- = x + (y + (x⋅z + y⋅z))
  -- = x + ((x⋅z + y⋅z) + y)
  -- = x + (x⋅z + (y⋅z + y))
  -- = (x + x⋅z) + (y⋅z + y)
  -- = (x + x⋅z) + (y + y⋅z)
  -- = x⋅𝐒(z) + y⋅𝐒(z)

[⋅]-with-[𝐒]ₗ : ∀{x y} → (𝐒(x) ⋅ y ≡ (x ⋅ y) + y)
[⋅]-with-[𝐒]ₗ {x}{y} =
  ([⋅][+]-distributivityᵣ-raw{x}{1}{y})
  🝖 ([≡]-with(expr ↦ (x ⋅ y) + expr) ([⋅]-identityₗ-raw {y}))
-- 𝐒(x)⋅y
-- = (x+1)⋅y
-- = x⋅y + 1⋅y
-- = x⋅y + y
-- TODO: Maybe this is the cause of a compiler error in Divisibility.Proof? {-# REWRITE [⋅]-with-[𝐒]ₗ #-}

[⋅]-with-[𝐒]ᵣ : ∀{x y} → x ⋅ 𝐒(y) ≡ x + (x ⋅ y)
[⋅]-with-[𝐒]ᵣ = [≡]-intro

postulate [⋅][+]-distributivityₗ-raw : Names.Distributivityₗ(_⋅_)(_+_)

postulate [⋅]-associativity-raw : Names.Associativity (_⋅_)
{-# REWRITE [⋅]-associativity-raw #-}

postulate [⋅]-commutativity-raw : Names.Commutativity (_⋅_)

-- testAssociativityOfSuccessor1 : ∀{x y} → ((x + 1) + y) ≡ (x + (1 + y))
-- testAssociativityOfSuccessor1 {x} {y} = [+]-associativity {x} {1} {y}

-- testAssociativityOfSuccessor2 : ∀{x y} → (𝐒(x) + y) ≡ (x + (1 + y))
-- testAssociativityOfSuccessor2 {x} {y} = [+]-associativity {x} {1} {y}

[𝐒]-injectivity-raw : Names.Injective(𝐒)
[𝐒]-injectivity-raw {0}    ([≡]-intro) = [≡]-intro
[𝐒]-injectivity-raw {𝐒(n)} (𝐒x≡𝐒y)     = [≡]-with(𝐏) 𝐒x≡𝐒y

[𝐒]-not-0 : ∀{n} → (𝐒(n) ≢ 𝟎)
[𝐒]-not-0 ()

[𝐏][𝐒]-identity : ∀{n} → (𝐏(𝐒(n)) ≡ n)
[𝐏][𝐒]-identity = [≡]-intro

[+]ₗ-injectivity-raw : ∀{a} → Names.Injective (_+ a)
[+]ₗ-injectivity-raw {0}    ( x₁+0≡x₂+0 ) = x₁+0≡x₂+0
[+]ₗ-injectivity-raw {𝐒(n)} (x₁+𝐒n≡x₂+𝐒n) = [+]ₗ-injectivity-raw {n} ([≡]-with(𝐏) x₁+𝐒n≡x₂+𝐒n)

-- TODO: Rename and generalize this (See commuteBoth in Structure.Operator.Properties)
commuteBothTemp : ∀{a₁ a₂ b₁ b₂} → (a₁ + a₂ ≡ b₁ + b₂) → (a₂ + a₁ ≡ b₂ + b₁)
commuteBothTemp {a₁} {a₂} {b₁} {b₂} a₁+a₂≡b₁+b₂ =
    (symmetry(_≡_) ([+]-commutativity-raw {a₁} {a₂}))
    🝖 a₁+a₂≡b₁+b₂
    🝖 ([+]-commutativity-raw {b₁} {b₂})

[+]ᵣ-injectivity-raw : ∀{a} → Names.Injective (a +_)
[+]ᵣ-injectivity-raw {0}    {x₁} {x₂} ( 0+x₁≡0+x₂ ) = commuteBothTemp {0} {x₁} {0} {x₂} 0+x₁≡0+x₂
[+]ᵣ-injectivity-raw {𝐒(n)} {x₁} {x₂} (𝐒n+x₁≡𝐒n+x₂) =
  [+]ᵣ-injectivity-raw {n} (
    commuteBothTemp {x₁} {n} {x₂} {n} ([≡]-with(𝐏) (commuteBothTemp {𝐒(n)} {x₁} {𝐒(n)} {x₂} 𝐒n+x₁≡𝐒n+x₂))
  )

[+]-sum-is-0ₗ : ∀{a b} → (a + b ≡ 0) → (a ≡ 0)
[+]-sum-is-0ₗ {a}{0}    a+0≡0 = a+0≡0
[+]-sum-is-0ₗ {a}{𝐒(n)} a+𝐒n≡0 = [+]-sum-is-0ₗ {a} {n} ([≡]-with(𝐏) a+𝐒n≡0)

[+]-sum-is-0ᵣ : ∀{a b} → (a + b ≡ 0) → (b ≡ 0)
[+]-sum-is-0ᵣ {b}{a} (b+a≡0) =
  ([+]-sum-is-0ₗ {a}{b}
    (
      ([+]-commutativity-raw {a}{b})
      🝖 (b+a≡0)
    )
  )

[+]-sum-is-0 : ∀{a b} → (a + b ≡ 0) → (a ≡ 0)∧(b ≡ 0)
[+]-sum-is-0 {a}{b} (proof) =
  ([∧]-intro
    ([+]-sum-is-0ₗ {a}{b} (proof))
    ([+]-sum-is-0ᵣ {a}{b} (proof))
  )

postulate [⋅]-product-is-1ₗ : ∀{a b} → (a ⋅ b ≡ 1) → (a ≡ 1)
postulate [⋅]-product-is-1ᵣ : ∀{a b} → (a ⋅ b ≡ 1) → (b ≡ 1)

[⋅]-product-is-0 : ∀{a b} → (a ⋅ b ≡ 0) → ((a ≡ 0)∨(b ≡ 0))
[⋅]-product-is-0 {a}{0} (_) = [∨]-introᵣ ([≡]-intro)
[⋅]-product-is-0 {0}{b} (_) = [∨]-introₗ ([≡]-intro)
[⋅]-product-is-0 {𝐒(a)}{𝐒(b)} (𝐒a⋅𝐒b≡0) =
  ([⊥]-elim
    ([𝐒]-not-0 {(𝐒(a) ⋅ b) + a}(
      ([+]-commutativity-raw {𝐒(a) ⋅ b}{𝐒(a)})
      🝖 (𝐒a⋅𝐒b≡0)
    ))
  )
  -- 𝐒a⋅𝐒b = 0 //assumption
  -- 𝐒a+(𝐒a⋅b) = 0 //Definition: (⋅)
  -- (𝐒a⋅b)+𝐒a = 0 //Commutativity (+)
  -- 𝐒((𝐒a⋅b)+a) = 0 //Definition: (+)
  -- ⊥ //∀n. 𝐒(n) ≠ 0
  -- (a = 0) ∨ (b = 0) //[⊥]-elim

-- [⋅]-divide : ∀{a b} → ((a ⌈/₀⌉ b) ⋅ b ≡ a)
-- [⋅]-divide : ∀{a b c} → (a ⋅ b ≡ c) → (a = c ⌈/₀⌉ b)

-- [⋅]-product-is-not-0 : ∀{a b n} → (a ⋅ b ≡ 𝐒(n)) → (∃(n₁ ↦ a ≡ 𝐒(n₁)) ∧ ∃(n₂ ↦ b ≡ 𝐒(n₂)))
-- [⋅]-product-is-not-0 {a}{0} (proof) = [⊥]-elim ([𝐒]-not-0 (symmetry proof))
-- [⋅]-product-is-not-0 {0}{b} (proof) = [⊥]-elim ([𝐒]-not-0 (symmetry proof))
-- [⋅]-product-is-not-0 {𝐒(a)}{𝐒(b)}{𝟎}    (𝐒a⋅𝐒b≡𝐒n) =
-- [⋅]-product-is-not-0 {𝐒(a)}{𝐒(b)}{𝐒(n)} (𝐒a⋅𝐒b≡𝐒n) =

-- [⋅]-product-is-coprime : ∀{a b} → Coprime(a ⋅ b) → ((a ≡ 1)∧(b ≡ a ⋅ b)) ∨ ((a ≡ a ⋅ b)∧(b ≡ 1))

-- Also called "The Division Algorithm" or "Euclides Algorithm"
-- TODO: Prove
-- [/]-uniqueness : ∀{a b} → ⦃ _ : b ≢ 0 ⦄ → ∃!{ℕ ⨯ ℕ}(\{(q , r) → ((a ≡ (b ⋅ q) + r) ∧ (0 ≤ r) ∧ (r < b))})

[+]-cancellationᵣ-raw : Names.Cancellationᵣ(_+_)
[+]-cancellationᵣ-raw {𝟎}    (rel) = rel
[+]-cancellationᵣ-raw {𝐒(x)} (rel) = [+]-cancellationᵣ-raw {x} ([≡]-with(𝐏) rel)

[+]-cancellationₗ-raw : Names.Cancellationₗ(_+_)
[+]-cancellationₗ-raw {𝟎}{a}{b} (rel) =
  (symmetry(_≡_) [+]-identityₗ-raw)
  🝖 (rel)
  🝖 ([+]-identityₗ-raw)

[+]-cancellationₗ-raw {𝐒(x)}{a}{b} (rel) =
  ([+]-cancellationₗ-raw {x}{a}{b}
    ([≡]-with(𝐏)(
      (symmetry(_≡_) ([+1]-commutativity {x}{a}))
      🝖 (rel)
      🝖 ([+1]-commutativity {x}{b})
    ))
  )

{-
  postulate [⋅]-cancellationₗ : ∀{x} → ⦃ _ : x ≢ 0 ⦄ → (Names.Cancellationₗ(_⋅_)){x}

  postulate [⋅]-cancellationᵣ : ∀{x} → ⦃ _ : x ≢ 0 ⦄ → (Names.Cancellationᵣ(_⋅_)){x}
-}

postulate [⋅][−₀]-distributivityₗ-raw : ∀{x y z : ℕ} → (x ⋅ (y −₀ z)) ≡ (x ⋅ y) −₀ (x ⋅ z)

postulate [⋅][−₀]-distributivityᵣ-raw : ∀{x y z : ℕ} → ((x −₀ y) ⋅ z) ≡ (x ⋅ z) −₀ (y ⋅ z)

[≤]ₗ[+] : ∀{x y : ℕ} → (x + y ≤ x) → (y ≡ 𝟎)
[≤]ₗ[+] {𝟎}               = [≤][0]ᵣ
[≤]ₗ[+] {𝐒(x)}{y} (proof) = [≤]ₗ[+] {x} ([≤]-without-[𝐒] {x + y} {x} (proof))

[−₀]-negative : ∀{x} → ((𝟎 −₀ x) ≡ 𝟎)
[−₀]-negative {𝟎}    = [≡]-intro
[−₀]-negative {𝐒(n)} = [≡]-intro
{-# REWRITE [−₀]-negative #-}

[−₀]-self : ∀{x} → ((x −₀ x) ≡ 𝟎)
[−₀]-self {𝟎}    = [≡]-intro
[−₀]-self {𝐒(n)} = [≡]-intro 🝖 ([−₀]-self{n})
{-# REWRITE [−₀]-self #-}

-- TODO: Is any of the directions true? Does not seem like
{-instance
  [𝐒]-of-[−₀] : ∀{x y z} → (𝐒(x −₀ y) ≡ z) → (𝐒(x) −₀ y ≡ z)
  [𝐒]-of-[−₀] {𝟎}   {𝟎} (proof) = proof
  [𝐒]-of-[−₀] {x}   {𝟎} (proof) = proof
  [𝐒]-of-[−₀] {𝟎}   {𝐒(y)} {𝟎} ()
  [𝐒]-of-[−₀] {𝟎}   {𝐒(y)} {𝐒(z)} ([≡]-intro) = [≡]-intro
  -- = PROVE where -- ([≡]-with(𝐒) proof) 🝖 (symmetry ([𝐒]-of-[−₀] {𝐒(𝟎)} {𝐒(y)} (proof)))
    -- postulate PROVE : ∀{y z} → (𝐒(𝟎 −₀ 𝐒(y)) ≡ z) → (𝐒(𝟎) −₀ 𝐒(y) ≡ z)
  -- 𝐒(𝟎 −₀ 𝐒(y)) ≡ 𝐒(z)
  -- ⇔ 𝐒(𝟎) ≡ 𝐒(z)
  -- ⇔ 𝟎 ≡ z

  -- 𝟎 ≡ 𝐒(z)
  -- ⇔ 𝟎 −₀ y ≡ 𝐒(z)
  -- ⇔ 𝐒(𝟎) −₀ 𝐒(y) ≡ 𝐒(z)
-}

[−₀]-self-[𝐒] : ∀{x} → ((𝐒(x) −₀ x) ≡ 𝐒(x −₀ x))
[−₀]-self-[𝐒] {𝟎}    = [≡]-intro
[−₀]-self-[𝐒] {𝐒(n)} = [−₀]-self-[𝐒] {n}
{-# REWRITE [−₀]-self-[𝐒] #-}

[−₀]-move-[𝐒] : ∀{x y} → (x ≥ y) → ((𝐒(x) −₀ y) ≡ 𝐒(x −₀ y))
[−₀]-move-[𝐒] {𝟎}   {𝟎}    _ = [≡]-intro
[−₀]-move-[𝐒] {𝟎}   {𝐒(_)} ()
[−₀]-move-[𝐒] {𝐒(_)}{𝟎}    _ = [≡]-intro
[−₀]-move-[𝐒] {𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = [−₀]-move-[𝐒] {x}{y} proof
  -- 𝐒𝐒x −₀ 𝐒y ≡ 𝐒(𝐒x −₀ 𝐒y)
  -- 𝐒x −₀ y ≡ 𝐒(x −₀ y)

[−₀]ₗ[+]ᵣ-nullify : ∀{x y} → ((x + y) −₀ y ≡ x)
[−₀]ₗ[+]ᵣ-nullify{𝟎}   {𝟎}    = [≡]-intro
[−₀]ₗ[+]ᵣ-nullify{x}   {𝐒(y)} = [≡]-intro 🝖 ([−₀]ₗ[+]ᵣ-nullify{x}{y})
[−₀]ₗ[+]ᵣ-nullify{𝐒(x)}{𝟎}    = [≡]-intro

[−₀]ₗ[+]ₗ-nullify : ∀{x y} → ((x + y) −₀ x ≡ y)
[−₀]ₗ[+]ₗ-nullify {x}{y} = [≡]-elimᵣ ([+]-commutativity-raw {y}{x}) {expr ↦ (expr −₀ x ≡ y)} ([−₀]ₗ[+]ᵣ-nullify {y}{x})

[−₀][+]ᵣ-nullify : ∀{x₁ x₂ y} → ((x₁ + y) −₀ (x₂ + y) ≡ x₁ −₀ x₂)
[−₀][+]ᵣ-nullify {_} {_} {𝟎}    = [≡]-intro
[−₀][+]ᵣ-nullify {x₁}{x₂}{𝐒(y)} = [−₀][+]ᵣ-nullify {x₁}{x₂}{y}

[−₀][+]ₗ-nullify : ∀{x y₁ y₂} → ((x + y₁) −₀ (x + y₂) ≡ y₁ −₀ y₂)
[−₀][+]ₗ-nullify {x}{y₁}{y₂} =
  [≡]-with-op(_−₀_) ([+]-commutativity-raw{x}{y₁}) ([+]-commutativity-raw{x}{y₂})
  🝖 [−₀][+]ᵣ-nullify{y₁}{y₂}{x}
{-# REWRITE [−₀][+]ₗ-nullify #-}

[−₀]-cases : ∀{x y} → ((x −₀ y) + y ≡ x) ∨ (x −₀ y ≡ 𝟎)
[−₀]-cases {𝟎}   {𝟎}    = [∨]-introᵣ [≡]-intro
[−₀]-cases {𝟎}   {𝐒(_)} = [∨]-introᵣ [≡]-intro
[−₀]-cases {𝐒(_)}{𝟎}    = [∨]-introₗ [≡]-intro
[−₀]-cases {𝐒(x)}{𝐒(y)} with [−₀]-cases {x}{y}
... | [∨]-introₗ proof = [∨]-introₗ ([≡]-with(𝐒) (proof))
... | [∨]-introᵣ proof = [∨]-introᵣ proof

[−₀]-cases-commuted : ∀{x y} → (y + (x −₀ y) ≡ x) ∨ (x −₀ y ≡ 𝟎)
[−₀]-cases-commuted {x}{y} with [−₀]-cases{x}{y}
... | [∨]-introₗ proof = [∨]-introₗ ([+]-commutativity-raw {y}{x −₀ y} 🝖 proof)
... | [∨]-introᵣ proof = [∨]-introᵣ proof
{-
[+][−₀]-commutativity : ∀{x y} → ⦃ _ : y ≥ z ⦄ → (x + (y −₀ z) ≡ (x −₀ z) + y)
-}

[−₀][+]-nullify2 : ∀{x y} → (x ≤ y) ↔ (x + (y −₀ x) ≡ y)
[−₀][+]-nullify2 {x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
  l : ∀{x y} → (x ≤ y) ← (x + (y −₀ x) ≡ y)
  l {𝟎}   {_}    _     = [≤]-minimum
  l {𝐒(_)}{𝟎}    ()
  l {𝐒(x)}{𝐒(y)} proof = [≤]-with-[𝐒] ⦃ l{x}{y} ([𝐒]-injectivity-raw proof) ⦄

  r : ∀{x y} → (x ≤ y) → (x + (y −₀ x) ≡ y)
  r {𝟎}   {𝟎}    proof = [≡]-intro
  r {𝟎}   {𝐒(_)} proof = [≡]-intro
  r {𝐒(_)}{𝟎}    ()
  r {𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = [≡]-with(𝐒) (r{x}{y} (proof))
  -- x + (y −₀ x) ≡ y
  -- ∃z. x + ((x + z) −₀ x) ≡ y
  -- ∃z. x + z ≡ y
  -- y ≡ y

[−₀]-comparison : ∀{x y} → (x ≤ y) ↔ (x −₀ y ≡ 𝟎)
[−₀]-comparison {x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
  l : ∀{x y} → (x ≤ y) ← (x −₀ y ≡ 𝟎)
  l {𝟎}   {_}    _     = [≤]-minimum
  l {𝐒(_)}{𝟎}    ()
  l {𝐒(x)}{𝐒(y)} proof = [≤]-with-[𝐒] ⦃ l{x}{y} proof ⦄

  r : ∀{x y} → (x ≤ y) → (x −₀ y ≡ 𝟎)
  r {𝟎}   {_}    proof = [≡]-intro
  r {𝐒(_)}{𝟎}    ()
  r {𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = r{x}{y} (proof)

-- TODO: One way to prove this is contraposition of [−₀]-comparison. Another is by [≤]-with-[+]ᵣ and some other stuff, but it seems to require more work
postulate [−₀]-when-non-zero : ∀{x y} → (x > y) ↔ (x −₀ y > 𝟎)

[−₀]-lesser-[𝐒]ₗ : ∀{x y} → ((x −₀ 𝐒(y)) ≤ (x −₀ y))
[−₀]-lesser-[𝐒]ᵣ : ∀{x y} → ((x −₀ y) ≤ (𝐒(x) −₀ y))

[−₀]-lesser-[𝐒]ₗ {𝟎}   {_}    = [≤]-minimum
[−₀]-lesser-[𝐒]ₗ {𝐒(_)}{𝟎}    = [≤]-of-[𝐒]
[−₀]-lesser-[𝐒]ₗ {𝐒(x)}{𝐒(y)} = [−₀]-lesser-[𝐒]ᵣ {x}{𝐒(y)}

[−₀]-lesser-[𝐒]ᵣ {𝟎}   {_}    = [≤]-minimum
[−₀]-lesser-[𝐒]ᵣ {𝐒(x)}{𝟎}    = [≤]-of-[𝐒]
[−₀]-lesser-[𝐒]ᵣ {𝐒(x)}{𝐒(y)} = [−₀]-lesser-[𝐒]ₗ {𝐒(x)}{y}

[≤][−₀][𝐒]ₗ : ∀{x y} → ((𝐒(x) −₀ y) ≤ 𝐒(x −₀ y))
[≤][−₀][𝐒]ₗ {x}   {𝟎}    = reflexivity(_≤_)
[≤][−₀][𝐒]ₗ {𝟎}   {𝐒(y)} = [≤]-minimum
[≤][−₀][𝐒]ₗ {𝐒(x)}{𝐒(y)} = [≤][−₀][𝐒]ₗ {x}{y}

[−₀]-lesser : ∀{x y} → ((x −₀ y) ≤ x)
[−₀]-lesser {𝟎}   {_}    = [≤]-minimum
[−₀]-lesser {𝐒(x)}{𝟎}    = reflexivity(_≤_)
[−₀]-lesser {𝐒(x)}{𝐒(y)} = ([−₀]-lesser-[𝐒]ₗ {𝐒(x)}{y}) 🝖 ([−₀]-lesser {𝐒(x)}{y})

[−₀]-positive : ∀{x y} → (y > x) → (y −₀ x > 0) -- TODO: Converse is probably also true
[−₀]-positive {𝟎}   {𝟎}    ()
[−₀]-positive {𝐒(x)}{𝟎}    ()
[−₀]-positive {𝟎}   {𝐒(y)} (_) = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄
[−₀]-positive {𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = [−₀]-positive {x}{y} (proof)
  -- (𝐒y > 𝐒x) → (𝐒y −₀ 𝐒x > 0)
  -- (𝐒x < 𝐒y) → (0 < 𝐒y −₀ 𝐒x)
  -- (𝐒𝐒x ≤ 𝐒y) → (𝐒0 ≤ 𝐒y −₀ 𝐒x)
  -- (𝐒x ≤ y) → (𝐒0 ≤ 𝐒y −₀ 𝐒x)
  -- (𝐒x ≤ y) → (𝐒0 ≤ y −₀ x)
  -- (x < y) → (0 < y −₀ x)
  -- (y > x) → (y −₀ x > 0)

[−₀]-nested-sameₗ : ∀{x y} → (x ≥ y) ↔ (x −₀ (x −₀ y) ≡ y)
[−₀]-nested-sameₗ {x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
  l : ∀{x y} → (x ≥ y) ← (x −₀ (x −₀ y) ≡ y)
  l {x}{y} proof =
    [≡]-to-[≤] (symmetry(_≡_) proof)
    🝖 [−₀]-lesser {x}{x −₀ y}

  r : ∀{x y} → (x ≥ y) → (x −₀ (x −₀ y) ≡ y)
  r{x}{y} x≥y =
    [≡]-with(_−₀ (x −₀ y)) (symmetry(_≡_) ([↔]-to-[→] ([−₀][+]-nullify2 {y}{x}) (x≥y)) 🝖 [+]-commutativity-raw{y}{x −₀ y})
    🝖 [−₀]ₗ[+]ₗ-nullify {x −₀ y}{y}
      -- x −₀ (x −₀ y)
      -- ((x −₀ y) + y) −₀ (x −₀ y)
      -- y

[𝄩]-identityₗ-raw : Names.Identityₗ (_𝄩_) (0)
[𝄩]-identityₗ-raw {𝟎}    = [≡]-intro
[𝄩]-identityₗ-raw {𝐒(_)} = [≡]-intro
{-# REWRITE [𝄩]-identityₗ-raw #-}

[𝄩]-identityᵣ-raw : Names.Identityᵣ (_𝄩_) (0)
[𝄩]-identityᵣ-raw {x} = [≡]-intro

[𝄩]-self : ∀{x} → (x 𝄩 x ≡ 𝟎)
[𝄩]-self {𝟎}    = [≡]-intro
[𝄩]-self {𝐒(x)} = [𝄩]-self {x}
{-# REWRITE [𝄩]-self #-}

[𝄩]-commutativity-raw : Names.Commutativity (_𝄩_)
[𝄩]-commutativity-raw{𝟎}   {𝟎}    = [≡]-intro
[𝄩]-commutativity-raw{𝟎}   {𝐒(y)} = [≡]-intro
[𝄩]-commutativity-raw{𝐒(x)}{𝟎}    = [≡]-intro
[𝄩]-commutativity-raw{𝐒(x)}{𝐒(y)} = [𝄩]-commutativity-raw{x}{y}

[𝄩]ₗ[+]ᵣ-nullify : ∀{x y} → ((x + y) 𝄩 y ≡ x)
[𝄩]ₗ[+]ᵣ-nullify{𝟎}   {𝟎}    = [≡]-intro
[𝄩]ₗ[+]ᵣ-nullify{x}   {𝐒(y)} = [≡]-intro 🝖 ([𝄩]ₗ[+]ᵣ-nullify{x}{y})
[𝄩]ₗ[+]ᵣ-nullify{𝐒(x)}{𝟎}    = [≡]-intro

[𝄩]ₗ[+]ₗ-nullify : ∀{x y} → ((x + y) 𝄩 x ≡ y)
[𝄩]ₗ[+]ₗ-nullify {x}{y} = [≡]-elimᵣ ([+]-commutativity-raw {y}{x}) {expr ↦ (expr 𝄩 x ≡ y)} ([𝄩]ₗ[+]ᵣ-nullify {y}{x})

[𝄩]ᵣ[+]ᵣ-nullify : ∀{x y} → (y 𝄩 (x + y) ≡ x)
[𝄩]ᵣ[+]ᵣ-nullify {x}{y} = transitivity(_≡_) ([𝄩]-commutativity-raw {y}{x + y}) ([𝄩]ₗ[+]ᵣ-nullify {x}{y})

[𝄩]ᵣ[+]ₗ-nullify : ∀{x y} → (x 𝄩 (x + y) ≡ y)
[𝄩]ᵣ[+]ₗ-nullify {x}{y} = transitivity(_≡_) ([𝄩]-commutativity-raw {x}{x + y}) ([𝄩]ₗ[+]ₗ-nullify {x}{y})

[𝄩]-with-[+]ᵣ : ∀{x y z} → ((x + z) 𝄩 (y + z) ≡ x 𝄩 y)
[𝄩]-with-[+]ᵣ {𝟎}   {𝟎}   {𝟎}    = [≡]-intro
[𝄩]-with-[+]ᵣ {𝟎}   {𝐒(y)}{𝟎}    = [≡]-intro
[𝄩]-with-[+]ᵣ {𝟎}   {𝟎}   {𝐒(z)} = [≡]-intro
[𝄩]-with-[+]ᵣ {𝟎}   {𝐒(y)}{𝐒(z)} = [𝄩]ᵣ[+]ᵣ-nullify {_}{z}
[𝄩]-with-[+]ᵣ {𝐒(x)}{𝟎}   {𝟎}    = [≡]-intro
[𝄩]-with-[+]ᵣ {𝐒(x)}{𝐒(y)}{𝟎}    = [≡]-intro
[𝄩]-with-[+]ᵣ {𝐒(x)}{𝟎}   {𝐒(z)} = [𝄩]ₗ[+]ᵣ-nullify {𝐒(x)}{𝐒(z)}
[𝄩]-with-[+]ᵣ {𝐒(x)}{𝐒(y)}{𝐒(z)} = [𝄩]-with-[+]ᵣ {𝐒(x)}{𝐒(y)}{z}

[𝄩]-with-[+]ₗ : ∀{x y z} → ((z + x) 𝄩 (z + y) ≡ x 𝄩 y)
[𝄩]-with-[+]ₗ {𝟎}   {𝟎}   {𝟎}    = [≡]-intro
[𝄩]-with-[+]ₗ {𝟎}   {𝐒(y)}{𝟎}    = [≡]-intro
[𝄩]-with-[+]ₗ {𝟎}   {𝟎}   {𝐒(z)} = [≡]-intro
[𝄩]-with-[+]ₗ {𝟎}   {𝐒(y)}{𝐒(z)} = [𝄩]ᵣ[+]ₗ-nullify {z}{𝐒(y)}
[𝄩]-with-[+]ₗ {𝐒(x)}{𝟎}   {𝟎}    = [≡]-intro
[𝄩]-with-[+]ₗ {𝐒(x)}{𝐒(y)}{𝟎}    = [≡]-intro
[𝄩]-with-[+]ₗ {𝐒(x)}{𝟎}   {𝐒(z)} = [𝄩]ₗ[+]ₗ-nullify {𝐒(z)}{𝐒(x)}
[𝄩]-with-[+]ₗ {𝐒(x)}{𝐒(y)}{𝐒(z)} = [𝄩]-with-[+]ₗ {𝐒(x)}{𝐒(y)}{z}

[𝄩]-equality : ∀{x y} → (x 𝄩 y ≡ 𝟎) → (x ≡ y)
[𝄩]-equality {𝟎}   {𝟎}    [≡]-intro = [≡]-intro
[𝄩]-equality {𝟎}   {𝐒(y)} ()
[𝄩]-equality {𝐒(x)}{𝟎}    ()
[𝄩]-equality {𝐒(x)}{𝐒(y)} proof     = [≡]-with(𝐒) ([𝄩]-equality {x}{y} proof)

{-
[𝄩]-associativity : Associativity (_𝄩_)
[𝄩]-associativity {x}{y}{z} = 
-}

instance
  [+]-identityₗ : Identityₗ (_+_) (0)
  Identityₗ.proof([+]-identityₗ) = [+]-identityₗ-raw

instance
  [+]-identityᵣ : Identityᵣ (_+_) (0)
  Identityᵣ.proof([+]-identityᵣ) = [+]-identityᵣ-raw

instance
  [+]-identity : Identity (_+_) (0)
  [+]-identity = intro

instance
  [+]-associativity : Associativity (_+_)
  Associativity.proof([+]-associativity) {x}{y}{z} = [+]-associativity-raw {x}{y}{z}

instance
  [+]-commutativity : Commutativity (_+_)
  Commutativity.proof([+]-commutativity) {x}{y} = [+]-commutativity-raw {x}{y}

instance
  [⋅]-absorberₗ : Absorberₗ (_⋅_) (0)
  Absorberₗ.proof([⋅]-absorberₗ) {x} = [⋅]-absorberₗ-raw {x}

instance
  [⋅]-absorberᵣ : Absorberᵣ (_⋅_) (0)
  Absorberᵣ.proof([⋅]-absorberᵣ) {x} = [⋅]-absorberᵣ-raw {x}

instance
  [⋅]-absorber : Absorber (_⋅_) (0)
  [⋅]-absorber = intro

instance
  [⋅]-identityₗ : Identityₗ (_⋅_) (1)
  Identityₗ.proof([⋅]-identityₗ) {x} = [⋅]-identityₗ-raw {x}

instance
  [⋅]-identityᵣ : Identityᵣ (_⋅_) (1)
  Identityᵣ.proof([⋅]-identityᵣ) {x} = [⋅]-identityᵣ-raw {x}

instance
  [⋅]-identity : Identity (_⋅_) (1)
  [⋅]-identity = intro

instance
  [⋅][+]-distributivityₗ : Distributivityₗ(_⋅_)(_+_)
  Distributivityₗ.proof([⋅][+]-distributivityₗ) {x}{y}{z} = [⋅][+]-distributivityₗ-raw {x}{y}{z}

instance
  [⋅][+]-distributivityᵣ : Distributivityᵣ(_⋅_)(_+_)
  Distributivityᵣ.proof([⋅][+]-distributivityᵣ) {x}{y}{z} = [⋅][+]-distributivityᵣ-raw {x}{y}{z}

instance
  [⋅]-associativity : Associativity (_⋅_)
  Associativity.proof([⋅]-associativity) {x}{y}{z} = [⋅]-associativity-raw {x}{y}{z}

instance
  [⋅]-commutativity : Commutativity (_⋅_)
  Commutativity.proof([⋅]-commutativity) {x}{y} = [⋅]-commutativity-raw {x}{y}

instance
  [𝄩]-commutativity : Commutativity (_𝄩_)
  Commutativity.proof([𝄩]-commutativity) {x}{y} = [𝄩]-commutativity-raw {x}{y}

instance
  [𝄩]-identityₗ : Identityₗ (_𝄩_) (𝟎)
  Identityₗ.proof([𝄩]-identityₗ) {x} = [𝄩]-identityₗ-raw {x}

instance
  [𝄩]-identityᵣ : Identityᵣ (_𝄩_) (𝟎)
  Identityᵣ.proof([𝄩]-identityᵣ) {x} = [𝄩]-identityᵣ-raw {x}

instance
  [𝄩]-identity : Identity (_𝄩_) (𝟎)
  [𝄩]-identity = intro

instance
  [⋅][−₀]-distributivityₗ : Distributivityₗ(_⋅_)(_−₀_)
  Distributivityₗ.proof([⋅][−₀]-distributivityₗ) {x}{y}{z} = [⋅][−₀]-distributivityₗ-raw {x}{y}{z}

instance
  [⋅][−₀]-distributivityᵣ : Distributivityᵣ(_⋅_)(_−₀_)
  Distributivityᵣ.proof([⋅][−₀]-distributivityᵣ) {x}{y}{z} = [⋅][−₀]-distributivityᵣ-raw {x}{y}{z}

instance
  [−₀]-absorberₗ : Absorberₗ (_−₀_) (𝟎)
  Absorberₗ.proof([−₀]-absorberₗ) {x} = [−₀]-negative {x}

instance
  [−₀]-identityᵣ : Identityᵣ (_−₀_) (𝟎)
  Identityᵣ.proof([−₀]-identityᵣ) {x} = [≡]-intro

instance
  [𝐒]-injectivity : Injective(𝐒)
  Injective.proof([𝐒]-injectivity) {n} = [𝐒]-injectivity-raw {n}

[+]ₗ-injectivity : ∀{a} → Injective (_+ a)
Injective.proof([+]ₗ-injectivity {a}) = [+]ₗ-injectivity-raw {a}

[+]ᵣ-injectivity : ∀{a} → Injective (a +_)
Injective.proof([+]ᵣ-injectivity {a}) = [+]ᵣ-injectivity-raw {a}
