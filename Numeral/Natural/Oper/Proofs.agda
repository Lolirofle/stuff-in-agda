module Numeral.Natural.Oper.Proofs where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Induction
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
-- open import Numeral.Natural.Relation.Order.Proofs
-- open import Numeral.Natural.Relation.Order.Classical
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Setoid.Uniqueness
open import Structure.Function.Domain
import      Structure.Function.Names as Names
open import Structure.Operator.Proofs.Util
open import Structure.Operator.Properties
import      Structure.Operator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Transitivity

[+]-identityₗ-raw : Names.Identityₗ (_+_) (0)
[+]-identityₗ-raw {x} = [ℕ]-inductionᵢ [≡]-intro (\{x} → [≡]-with(𝐒) {𝟎 + x}{x}) {x}
{-# REWRITE [+]-identityₗ-raw #-}

instance
  [+]-identityₗ : Identityₗ (_+_) (0)
  Identityₗ.proof([+]-identityₗ) = [+]-identityₗ-raw

[+]-identityᵣ-raw : Names.Identityᵣ (_+_) (0)
[+]-identityᵣ-raw {x} = [ℕ]-inductionᵢ [≡]-intro (\{x} → [≡]-with(𝐒) {x + 𝟎}{x}) {x}

instance
  [+]-identityᵣ : Identityᵣ (_+_) (0)
  Identityᵣ.proof([+]-identityᵣ) = [+]-identityᵣ-raw

[+]-associativity-raw : Names.Associativity (_+_)
[+]-associativity-raw {x}{y}{z} = [ℕ]-inductionᵢ [≡]-intro (\{i} → [≡]-with(𝐒) {(x + y) + i} {x + (y + i)}) {z}

instance
  [+]-associativity : Associativity (_+_)
  Associativity.proof([+]-associativity) {x}{y}{z} = [+]-associativity-raw {x}{y}{z}

[+1]-commutativity : ∀{x y : ℕ} → (𝐒(x) + y) ≡ (x + 𝐒(y))
[+1]-commutativity {x}{y} = [ℕ]-induction [≡]-intro (\i → [≡]-with(𝐒) {𝐒(x) + i} {x + 𝐒(i)}) {y}
{-# REWRITE [+1]-commutativity #-}

[+]-commutativity-raw : Names.Commutativity (_+_)
[+]-commutativity-raw {x}{y} = [ℕ]-induction base next {y} where
  base = [+]-identityᵣ-raw 🝖 symmetry(_≡_) [+]-identityₗ-raw
  next = \i eq → ([≡]-with(𝐒) {x + i}{i + x} eq) 🝖 symmetry(_≡_) ([+1]-commutativity {i}{x})

[+1]-and-[𝐒] : ∀{x : ℕ} → (x + 1 ≡ 𝐒(x))
[+1]-and-[𝐒] {x} = [≡]-intro

[1+]-and-[𝐒] : ∀{x : ℕ} → (1 + x ≡ 𝐒(x))
[1+]-and-[𝐒] {x} = [+1]-and-[𝐒] {x} 🝖 [+]-commutativity-raw {x}{1}

[⋅]-absorberₗ-raw : Names.Absorberₗ (_⋅_) (0)
[⋅]-absorberₗ-raw {x} = [ℕ]-induction [≡]-intro (\i → [≡]-with(0 +_) {0 ⋅ i}{0}) {x}
{-# REWRITE [⋅]-absorberₗ-raw #-}

[⋅]-absorberᵣ-raw : Names.Absorberᵣ (_⋅_) (0)
[⋅]-absorberᵣ-raw = [≡]-intro

[⋅]-identityₗ-raw : Names.Identityₗ (_⋅_) (1)
[⋅]-identityₗ-raw {x} = [ℕ]-induction [≡]-intro (\i eq → ([+]-commutativity-raw {1} {1 ⋅ i}) 🝖 ([≡]-with(𝐒) {_}{i} eq)) {x}
{-# REWRITE [⋅]-identityₗ-raw #-}

[⋅]-identityᵣ-raw : Names.Identityᵣ (_⋅_) (1)
[⋅]-identityᵣ-raw = [≡]-intro

[⋅][+]-distributivityᵣ-raw : Names.Distributivityᵣ(_⋅_)(_+_)
[⋅][+]-distributivityᵣ-raw {x}{y}{z} = [ℕ]-induction [≡]-intro next {z} where
  next : ∀(z : ℕ) → ((x + y) ⋅ z) ≡ ((x ⋅ z) + (y ⋅ z)) → ((x + y) ⋅ 𝐒(z)) ≡ ((x ⋅ 𝐒(z)) + (y ⋅ 𝐒(z)))
  next z proof = ([≡]-with((x + y) +_) proof) 🝖 (One.associate-commute4 {a = x}{y}{x ⋅ z}{y ⋅ z} ([+]-commutativity-raw{x = y}))

[⋅]-with-[𝐒]ₗ : ∀{x y} → (𝐒(x) ⋅ y ≡ (x ⋅ y) + y)
[⋅]-with-[𝐒]ₗ {x}{y} = ([⋅][+]-distributivityᵣ-raw{x}{1}{y}) 🝖 ([≡]-with(expr ↦ (x ⋅ y) + expr) ([⋅]-identityₗ-raw {y}))

[⋅]-with-[𝐒]ᵣ : ∀{x y} → x ⋅ 𝐒(y) ≡ x + (x ⋅ y)
[⋅]-with-[𝐒]ᵣ = [≡]-intro

[⋅][+]-distributivityₗ-raw : Names.Distributivityₗ(_⋅_)(_+_)
[⋅][+]-distributivityₗ-raw {𝟎}   {y}   {z}   = [≡]-intro
[⋅][+]-distributivityₗ-raw {𝐒 x} {𝟎}   {z}   = [≡]-intro
[⋅][+]-distributivityₗ-raw {𝐒 x} {𝐒 y} {𝟎}   = [≡]-intro
[⋅][+]-distributivityₗ-raw {𝐒 x} {𝐒 y} {𝐒 z} = [≡]-with(𝐒 ∘ 𝐒) $
  x + (x + (𝐒 x ⋅ (y + z)))         🝖[ _≡_ ]-[ [≡]-with((x +_) ∘ (x +_)) ([⋅][+]-distributivityₗ-raw {𝐒 x} {y} {z}) ]
  x + (x + ((𝐒 x ⋅ y) + (𝐒 x ⋅ z))) 🝖[ _≡_ ]-[ [≡]-with(x +_) (One.commuteₗ-assocᵣ ⦃ comm = intro(\{x y} → [+]-commutativity-raw {x}{y}) ⦄ {a = x}{b = 𝐒 x ⋅ y}{c = 𝐒 x ⋅ z}) ]
  x + ((𝐒 x ⋅ y) + (x + (𝐒 x ⋅ z))) 🝖[ _≡_ ]-[ [+]-associativity-raw {x = x}{y = 𝐒 x ⋅ y} ]-sym
  (x + (𝐒 x ⋅ y)) + (x + (𝐒 x ⋅ z)) 🝖-end

[⋅]-associativity-raw : Names.Associativity (_⋅_)
[⋅]-associativity-raw {𝟎}   {𝟎}   {𝟎}   = [≡]-intro
[⋅]-associativity-raw {𝟎}   {𝟎}   {𝐒 z} = [≡]-intro
[⋅]-associativity-raw {𝟎}   {𝐒 y} {𝟎}   = [≡]-intro
[⋅]-associativity-raw {𝟎}   {𝐒 y} {𝐒 z} = [≡]-intro
[⋅]-associativity-raw {𝐒 x} {𝟎}   {𝟎}   = [≡]-intro
[⋅]-associativity-raw {𝐒 x} {𝟎}   {𝐒 z} = [≡]-intro
[⋅]-associativity-raw {𝐒 x} {𝐒 y} {𝟎}   = [≡]-intro
[⋅]-associativity-raw {𝐒 x} {𝐒 y} {𝐒 z} = [≡]-with(𝐒) $
  (x + (𝐒 x ⋅ y)) + (𝐒(x + 𝐒 x ⋅ y) ⋅ z)  🝖[ _≡_ ]-[ [+]-associativity-raw {x = x}{y = 𝐒 x ⋅ y} ]
  x + ((𝐒 x ⋅ y) + (𝐒(x + 𝐒 x ⋅ y) ⋅ z))  🝖[ _≡_ ]-[]
  x + ((𝐒 x ⋅ y) + ((𝐒 x + 𝐒 x ⋅ y) ⋅ z)) 🝖[ _≡_ ]-[]
  x + ((𝐒 x ⋅ y) + ((𝐒 x ⋅ 𝐒 y) ⋅ z))     🝖[ _≡_ ]-[ [≡]-with(expr ↦ x + ((𝐒 x ⋅ y) + expr)) ([⋅]-associativity-raw {𝐒 x}{𝐒 y}{z}) ]
  x + ((𝐒 x ⋅ y) + (𝐒 x ⋅ (𝐒 y ⋅ z)))     🝖[ _≡_ ]-[ [≡]-with(x +_) ([⋅][+]-distributivityₗ-raw {x = 𝐒 x}{y = y}{z = 𝐒 y ⋅ z}) ]-sym
  x + (𝐒 x ⋅ (y + (𝐒 y ⋅ z)))             🝖-end

[⋅]-commutativity-raw : Names.Commutativity (_⋅_)
[⋅]-commutativity-raw {𝟎} {𝟎} = [≡]-intro
[⋅]-commutativity-raw {𝟎} {𝐒 y} = [≡]-intro
[⋅]-commutativity-raw {𝐒 x} {𝟎} = [≡]-intro
[⋅]-commutativity-raw {𝐒 x} {𝐒 y} = [≡]-with(𝐒) $
  x + (𝐒 x ⋅ y)     🝖-[ [≡]-with(x +_) ([⋅]-with-[𝐒]ₗ {x}{y}) ]
  x + ((x ⋅ y) + y) 🝖-[ [≡]-with(x +_) ([+]-commutativity-raw {x ⋅ y}{y}) ]
  x + (y + (x ⋅ y)) 🝖-[ One.commuteₗ-assocᵣ ⦃ comm = intro(\{x y} → [+]-commutativity-raw {x}{y}) ⦄ {a = x}{b = y}{c = x ⋅ y} ]
  y + (x + (x ⋅ y)) 🝖-[ [≡]-with(expr ↦ y + (x + expr)) ([⋅]-commutativity-raw {x} {y}) ]
  y + (x + (y ⋅ x)) 🝖-[ [≡]-with(y +_) ([+]-commutativity-raw {x}{y ⋅ x}) ]
  y + ((y ⋅ x) + x) 🝖-[ [≡]-with(y +_) ([⋅]-with-[𝐒]ₗ {y}{x}) ]-sym
  y + (𝐒 y ⋅ x)     🝖-end

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

[+]ᵣ-injectivity-raw : ∀{a} → Names.Injective (a +_)
[+]ᵣ-injectivity-raw {0}    {x₁} {x₂} ( 0+x₁≡0+x₂ ) = One.commuteBothTemp ⦃ comm = intro(\{x y} → [+]-commutativity-raw {x}{y}) ⦄ {0} {x₁} {0} {x₂} 0+x₁≡0+x₂
[+]ᵣ-injectivity-raw {𝐒(n)} {x₁} {x₂} (𝐒n+x₁≡𝐒n+x₂) =
  [+]ᵣ-injectivity-raw {n} (
    One.commuteBothTemp ⦃ comm = intro(\{x y} → [+]-commutativity-raw {x}{y}) ⦄ {x₁} {n} {x₂} {n} ([≡]-with(𝐏) (One.commuteBothTemp ⦃ comm = intro(\{x y} → [+]-commutativity-raw {x}{y}) ⦄ {𝐒(n)} {x₁} {𝐒(n)} {x₂} 𝐒n+x₁≡𝐒n+x₂))
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

[⋅]-product-is-1ₗ : ∀{a b} → (a ⋅ b ≡ 1) → (a ≡ 1)
[⋅]-product-is-1ₗ {𝟎}   {_}   p = p
[⋅]-product-is-1ₗ {𝐒 a} {𝟎}   ()
[⋅]-product-is-1ₗ {𝐒 a} {𝐒 b} p = [≡]-with(𝐒) ([+]-sum-is-0ₗ ([𝐒]-injectivity-raw p))

[⋅]-product-is-1ᵣ : ∀{a b} → (a ⋅ b ≡ 1) → (b ≡ 1)
[⋅]-product-is-1ᵣ {a}{b} p = [⋅]-product-is-1ₗ {b}{a} ([⋅]-commutativity-raw{b}{a} 🝖 p)

[⋅]-product-is-0 : ∀{a b} → (a ⋅ b ≡ 0) → ((a ≡ 0)∨(b ≡ 0))
[⋅]-product-is-0 {a}{0}    (_) = [∨]-introᵣ ([≡]-intro)
[⋅]-product-is-0 {0}{𝐒(b)} (_) = [∨]-introₗ ([≡]-intro)
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

postulate [⋅]-cancellationₗ : ∀{x} → ⦃ _ : Positive(x) ⦄ → (Names.CancellationOnₗ(_⋅_)(x))

postulate [⋅]-cancellationᵣ : ∀{x} → ⦃ _ : Positive(x) ⦄ → (Names.CancellationOnᵣ(_⋅_)(x))
{-[⋅]-cancellationᵣ {𝟎}       ⦃ nx0 ⦄ {y₁}   {y₂}   p with () ← nx0 p
[⋅]-cancellationᵣ {𝐒 𝟎}     ⦃ nx0 ⦄ {y₁}   {y₂}   p = p
[⋅]-cancellationᵣ {𝐒 (𝐒 x)} ⦃ nx0 ⦄ {𝟎}    {𝟎}    p = [≡]-intro
[⋅]-cancellationᵣ {𝐒 (𝐒 x)} ⦃ nx0 ⦄ {𝐒 y₁} {𝐒 y₂} p = {!!}
-- [⋅]-cancellationᵣ {𝐒 (𝐒 x)} ⦃ nx0 ⦄ {𝐒 y₁} {𝐒 y₂} p = congruence₁(𝐒) ([⋅]-cancellationᵣ {𝐒 x} ⦃ [𝐒]-not-0 ⦄ {y₁} {y₂} {![𝐒]-injectivity-raw([𝐒]-injectivity-raw p)!})
-}

postulate [^]-with-𝟎ₗ : ∀{x} → (𝟎 ^ x ≡ 𝟎)

postulate [^]-with-[𝐒]ₗ : ∀{x y} → (𝐒(x) ^ y ≡ (x ^ y) ⋅ y)
-- [^]-with-[𝐒]ₗ = {!!}

postulate [⋅][−₀]-distributivityₗ-raw : ∀{x y z : ℕ} → (x ⋅ (y −₀ z)) ≡ (x ⋅ y) −₀ (x ⋅ z)

postulate [⋅][−₀]-distributivityᵣ-raw : ∀{x y z : ℕ} → ((x −₀ y) ⋅ z) ≡ (x ⋅ z) −₀ (y ⋅ z)

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
  -- = PROVE where -- (congruence₁(𝐒) proof) 🝖 (symmetry ([𝐒]-of-[−₀] {𝐒(𝟎)} {𝐒(y)} (proof)))
    -- postulate PROVE : ∀{y z} → (𝐒(𝟎 −₀ 𝐒(y)) ≡ z) → (𝐒(𝟎) −₀ 𝐒(y) ≡ z)
  -- 𝐒(𝟎 −₀ 𝐒(y)) ≡ 𝐒(z)
  -- ⇔ 𝐒(𝟎) ≡ 𝐒(z)
  -- ⇔ 𝟎 ≡ z

  -- 𝟎 ≡ 𝐒(z)
  -- ⇔ 𝟎 −₀ y ≡ 𝐒(z)
  -- ⇔ 𝐒(𝟎) −₀ 𝐒(y) ≡ 𝐒(z)
-}

[−₀]-with-[𝐒]ᵣ : ∀{x y} → ((x −₀ 𝐒(y)) ≡ 𝐏(x −₀ y))
[−₀]-with-[𝐒]ᵣ {𝟎} {𝟎}     = [≡]-intro
[−₀]-with-[𝐒]ᵣ {𝟎} {𝐒 y}   = [≡]-intro
[−₀]-with-[𝐒]ᵣ {𝐒 x} {𝟎}   = [≡]-intro
[−₀]-with-[𝐒]ᵣ {𝐒 x} {𝐒 y} = [−₀]-with-[𝐒]ᵣ {x} {y}

[−₀]ₗ[+]ᵣ-nullify : ∀{x y} → ((x + y) −₀ y ≡ x)
[−₀]ₗ[+]ᵣ-nullify{𝟎}   {𝟎}    = [≡]-intro
[−₀]ₗ[+]ᵣ-nullify{𝟎}   {𝐒(y)} = [≡]-intro
[−₀]ₗ[+]ᵣ-nullify{𝐒(x)}{𝐒(y)} = [≡]-intro 🝖 ([−₀]ₗ[+]ᵣ-nullify{𝐒(x)}{y})
[−₀]ₗ[+]ᵣ-nullify{𝐒(x)}{𝟎}    = [≡]-intro

[−₀]ₗ[+]ₗ-nullify : ∀{x y} → ((x + y) −₀ x ≡ y)
[−₀]ₗ[+]ₗ-nullify {x}{y} = [≡]-substitutionᵣ ([+]-commutativity-raw {y}{x}) {expr ↦ (expr −₀ x ≡ y)} ([−₀]ₗ[+]ᵣ-nullify {y}{x})

[−₀][+]ᵣ-nullify : ∀{x₁ x₂ y} → ((x₁ + y) −₀ (x₂ + y) ≡ x₁ −₀ x₂)
[−₀][+]ᵣ-nullify {_} {_} {𝟎}    = [≡]-intro
[−₀][+]ᵣ-nullify {x₁}{x₂}{𝐒(y)} = [−₀][+]ᵣ-nullify {x₁}{x₂}{y}

[−₀][+]ₗ-nullify : ∀{x y₁ y₂} → ((x + y₁) −₀ (x + y₂) ≡ y₁ −₀ y₂)
[−₀][+]ₗ-nullify {x}{y₁}{y₂} =
  [≡]-with-op(_−₀_) ([+]-commutativity-raw{x}{y₁}) ([+]-commutativity-raw{x}{y₂})
  🝖 [−₀][+]ᵣ-nullify{y₁}{y₂}{x}

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

[𝄩]-identityₗ-raw : Names.Identityₗ (_𝄩_) (0)
[𝄩]-identityₗ-raw {𝟎}    = [≡]-intro
[𝄩]-identityₗ-raw {𝐒(_)} = [≡]-intro
{-# REWRITE [𝄩]-identityₗ-raw #-}

[𝄩]-identityᵣ-raw : Names.Identityᵣ (_𝄩_) (0)
[𝄩]-identityᵣ-raw {𝟎}    = [≡]-intro
[𝄩]-identityᵣ-raw {𝐒(_)} = [≡]-intro
{-# REWRITE [𝄩]-identityᵣ-raw #-}

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
[𝄩]ₗ[+]ᵣ-nullify{𝟎}   {𝐒(y)} = [≡]-intro
[𝄩]ₗ[+]ᵣ-nullify{𝐒(x)}{𝐒(y)} = [≡]-intro 🝖 ([𝄩]ₗ[+]ᵣ-nullify{𝐒(x)}{y})
[𝄩]ₗ[+]ᵣ-nullify{𝐒(x)}{𝟎}    = [≡]-intro

[𝄩]ₗ[+]ₗ-nullify : ∀{x y} → ((x + y) 𝄩 x ≡ y)
[𝄩]ₗ[+]ₗ-nullify {x}{y} = [≡]-substitutionᵣ ([+]-commutativity-raw {y}{x}) {expr ↦ (expr 𝄩 x ≡ y)} ([𝄩]ₗ[+]ᵣ-nullify {y}{x})

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

instance
  [+]-identity : Identity (_+_) (0)
  [+]-identity = intro

instance
  [+]-commutativity : Commutativity (_+_)
  Commutativity.proof([+]-commutativity) {x}{y} = [+]-commutativity-raw {x}{y}

instance
  [+]-cancellationₗ : Cancellationₗ (_+_)
  Cancellationₗ.proof([+]-cancellationₗ) {x}{y} = [+]-cancellationₗ-raw {x}{y}

instance
  [+]-cancellationᵣ : Cancellationᵣ (_+_)
  Cancellationᵣ.proof([+]-cancellationᵣ) {x}{y} = [+]-cancellationᵣ-raw {x}{y}

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
  [⋅][−₀]-distributivityₗ : Distributivityₗ(_⋅_)(_−₀_)
  Distributivityₗ.proof([⋅][−₀]-distributivityₗ) {x}{y}{z} = [⋅][−₀]-distributivityₗ-raw {x}{y}{z}

instance
  [⋅][−₀]-distributivityᵣ : Distributivityᵣ(_⋅_)(_−₀_)
  Distributivityᵣ.proof([⋅][−₀]-distributivityᵣ) {x}{y}{z} = [⋅][−₀]-distributivityᵣ-raw {x}{y}{z}

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
