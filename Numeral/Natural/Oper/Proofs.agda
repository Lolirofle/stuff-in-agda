module Numeral.Natural.Oper.Proofs where

import Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Induction
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator
open import Structure.Operator.Proofs.Util
open import Structure.Operator.Properties
import      Structure.Operator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Transitivity

-- TODO: For old code
open import Numeral.Natural.Proofs public
open import Numeral.Natural.Oper.Proofs.Rewrite public

instance
  [+]-identityₗ : Identityₗ(_+_)(0)
  Identityₗ.proof([+]-identityₗ) = [+]-baseₗ

instance
  [+]-identityᵣ : Identityᵣ(_+_)(0)
  Identityᵣ.proof([+]-identityᵣ) {x} = ℕ-elim [≡]-intro (x ↦ [≡]-with(𝐒) {x + 𝟎}{x}) x

instance
  [+]-identity : Identity (_+_) (0)
  [+]-identity = intro

instance
  [+]-associativity : Associativity(_+_)
  Associativity.proof([+]-associativity) {x}{y}{z} = ℕ-elim [≡]-intro (i ↦ [≡]-with(𝐒) {(x + y) + i} {x + (y + i)}) z

instance
  [+]-commutativity : Commutativity (_+_)
  Commutativity.proof([+]-commutativity) {x}{y} = ℕ-elim base next y where
    base = identityᵣ(_+_)(𝟎) 🝖 symmetry(_≡_) (identityₗ(_+_)(𝟎))
    next = \i eq → ([≡]-with(𝐒) {x + i}{i + x} eq) 🝖 symmetry(_≡_) ([+]-stepₗ {i}{x})

[+1]-and-[𝐒] : ∀{x : ℕ} → (x + 1 ≡ 𝐒(x))
[+1]-and-[𝐒] {x} = [≡]-intro

[1+]-and-[𝐒] : ∀{x : ℕ} → (1 + x ≡ 𝐒(x))
[1+]-and-[𝐒] {x} = [+1]-and-[𝐒] {x} 🝖 commutativity(_+_) {x}{1}

[⋅]-absorberₗ-raw : Names.Absorberₗ(_⋅_)(0)
[⋅]-absorberₗ-raw {x} = ℕ-elim [≡]-intro (\i → [≡]-with(0 +_) {0 ⋅ i}{0}) x
{-# REWRITE [⋅]-absorberₗ-raw #-}
instance
  [⋅]-absorberₗ : Absorberₗ(_⋅_)(0)
  Absorberₗ.proof([⋅]-absorberₗ) {x} = [⋅]-absorberₗ-raw {x}

instance
  [⋅]-absorberᵣ : Absorberᵣ(_⋅_)(0)
  Absorberᵣ.proof([⋅]-absorberᵣ) {x} = [≡]-intro

instance
  [⋅]-absorber : Absorber(_⋅_)(0)
  [⋅]-absorber = intro

[⋅]-identityₗ-raw : Names.Identityₗ(_⋅_)(1)
[⋅]-identityₗ-raw {x} = ℕ-elim [≡]-intro (\i eq → (commutativity(_+_) {1} {1 ⋅ i}) 🝖 ([≡]-with(𝐒) {_}{i} eq)) x
{-# REWRITE [⋅]-identityₗ-raw #-}
instance
  [⋅]-identityₗ : Identityₗ(_⋅_)(1)
  Identityₗ.proof([⋅]-identityₗ) {x} = [⋅]-identityₗ-raw {x}

instance
  [⋅]-identityᵣ : Identityᵣ(_⋅_)(1)
  Identityᵣ.proof([⋅]-identityᵣ) = [≡]-intro

instance
  [⋅]-identity : Identity(_⋅_)(1)
  [⋅]-identity = intro

instance
  [⋅][+]-distributivityᵣ : Distributivityᵣ(_⋅_)(_+_)
  Distributivityᵣ.proof([⋅][+]-distributivityᵣ) {x}{y}{z} = ℕ-elim [≡]-intro next z where
    next : ∀(z : ℕ) → ((x + y) ⋅ z) ≡ ((x ⋅ z) + (y ⋅ z)) → ((x + y) ⋅ 𝐒(z)) ≡ ((x ⋅ 𝐒(z)) + (y ⋅ 𝐒(z)))
    next z proof = ([≡]-with((x + y) +_) proof) 🝖 (One.associate-commute4 {a = x}{y}{x ⋅ z}{y ⋅ z} (commutativity(_+_){x = y}))

[⋅]-with-[𝐒]ₗ : ∀{x y} → (𝐒(x) ⋅ y ≡ (x ⋅ y) + y)
[⋅]-with-[𝐒]ₗ {x}{y} = (distributivityᵣ(_⋅_)(_+_) {x}{1}{y}) 🝖 ([≡]-with(expr ↦ (x ⋅ y) + expr) ([⋅]-identityₗ-raw {y}))

[⋅]-with-[𝐒]ᵣ : ∀{x y} → (x ⋅ 𝐒(y) ≡ x + (x ⋅ y))
[⋅]-with-[𝐒]ᵣ = [≡]-intro

instance
  [⋅][+]-distributivityₗ : Distributivityₗ(_⋅_)(_+_)
  Distributivityₗ.proof([⋅][+]-distributivityₗ) {x}{y}{z} = p{x}{y}{z} where
    p : Names.Distributivityₗ(_⋅_)(_+_)
    p {𝟎}   {y}   {z}   = [≡]-intro
    p {𝐒 x} {𝟎}   {z}   = [≡]-intro
    p {𝐒 x} {𝐒 y} {𝟎}   = [≡]-intro
    p {𝐒 x} {𝐒 y} {𝐒 z} = [≡]-with(𝐒 ∘ 𝐒) $
      x + (x + (𝐒 x ⋅ (y + z)))         🝖[ _≡_ ]-[ [≡]-with((x +_) ∘ (x +_)) (p {𝐒 x} {y} {z}) ]
      x + (x + ((𝐒 x ⋅ y) + (𝐒 x ⋅ z))) 🝖[ _≡_ ]-[ [≡]-with(x +_) (One.commuteₗ-assocᵣ ⦃ comm = intro(\{x y} → commutativity(_+_) {x}{y}) ⦄ {a = x}{b = 𝐒 x ⋅ y}{c = 𝐒 x ⋅ z}) ]
      x + ((𝐒 x ⋅ y) + (x + (𝐒 x ⋅ z))) 🝖[ _≡_ ]-[ associativity(_+_) {x = x}{y = 𝐒 x ⋅ y} ]-sym
      (x + (𝐒 x ⋅ y)) + (x + (𝐒 x ⋅ z)) 🝖-end

instance
  [⋅]-associativity : Associativity (_⋅_)
  Associativity.proof([⋅]-associativity) {x}{y}{z} = p{x}{y}{z} where
    p : Names.Associativity(_⋅_)
    p {𝟎}   {𝟎}   {𝟎}   = [≡]-intro
    p {𝟎}   {𝟎}   {𝐒 z} = [≡]-intro
    p {𝟎}   {𝐒 y} {𝟎}   = [≡]-intro
    p {𝟎}   {𝐒 y} {𝐒 z} = [≡]-intro
    p {𝐒 x} {𝟎}   {𝟎}   = [≡]-intro
    p {𝐒 x} {𝟎}   {𝐒 z} = [≡]-intro
    p {𝐒 x} {𝐒 y} {𝟎}   = [≡]-intro
    p {𝐒 x} {𝐒 y} {𝐒 z} = [≡]-with(𝐒) $
      (x + (𝐒 x ⋅ y)) + (𝐒(x + 𝐒 x ⋅ y) ⋅ z)  🝖[ _≡_ ]-[ associativity(_+_) {x = x}{y = 𝐒 x ⋅ y} ]
      x + ((𝐒 x ⋅ y) + (𝐒(x + 𝐒 x ⋅ y) ⋅ z))  🝖[ _≡_ ]-[]
      x + ((𝐒 x ⋅ y) + ((𝐒 x + 𝐒 x ⋅ y) ⋅ z)) 🝖[ _≡_ ]-[]
      x + ((𝐒 x ⋅ y) + ((𝐒 x ⋅ 𝐒 y) ⋅ z))     🝖[ _≡_ ]-[ [≡]-with(expr ↦ x + ((𝐒 x ⋅ y) + expr)) (p{𝐒 x}{𝐒 y}{z}) ]
      x + ((𝐒 x ⋅ y) + (𝐒 x ⋅ (𝐒 y ⋅ z)))     🝖[ _≡_ ]-[ [≡]-with(x +_) (distributivityₗ(_⋅_)(_+_) {x = 𝐒 x}{y = y}{z = 𝐒 y ⋅ z}) ]-sym
      x + (𝐒 x ⋅ (y + (𝐒 y ⋅ z)))             🝖-end

instance
  [⋅]-commutativity : Commutativity (_⋅_)
  Commutativity.proof([⋅]-commutativity) {x}{y} = p {x}{y} where
    p : Names.Commutativity(_⋅_)
    p {𝟎} {𝟎} = [≡]-intro
    p {𝟎} {𝐒 y} = [≡]-intro
    p {𝐒 x} {𝟎} = [≡]-intro
    p {𝐒 x} {𝐒 y} = [≡]-with(𝐒) $
      x + (𝐒 x ⋅ y)     🝖-[ [≡]-with(x +_) ([⋅]-with-[𝐒]ₗ {x}{y}) ]
      x + ((x ⋅ y) + y) 🝖-[ [≡]-with(x +_) (commutativity(_+_) {x ⋅ y}{y}) ]
      x + (y + (x ⋅ y)) 🝖-[ One.commuteₗ-assocᵣ ⦃ comm = intro(\{x y} → commutativity(_+_) {x}{y}) ⦄ {a = x}{b = y}{c = x ⋅ y} ]
      y + (x + (x ⋅ y)) 🝖-[ [≡]-with(expr ↦ y + (x + expr)) (p {x} {y}) ]
      y + (x + (y ⋅ x)) 🝖-[ [≡]-with(y +_) (commutativity(_+_) {x}{y ⋅ x}) ]
      y + ((y ⋅ x) + x) 🝖-[ [≡]-with(y +_) ([⋅]-with-[𝐒]ₗ {y}{x}) ]-sym
      y + (𝐒 y ⋅ x)     🝖-end

[𝐏][𝐒]-inverses : ∀{n} → (𝐏(𝐒(n)) ≡ n)
[𝐏][𝐒]-inverses = [≡]-intro

[+]-sum-is-0 : ∀{a b} → (a + b ≡ 0) → (a ≡ 0)∧(b ≡ 0)
[+]-sum-is-0 {a}{b} proof = [∧]-intro (l{a}{b} proof) r where
  l = \{a b} → ℕ-elim{T = \b → (a + b ≡ 0) → (a ≡ 0)} id (\_ p → p ∘ [≡]-with(𝐏)) b
  r = l{b}{a} (commutativity(_+_) {b}{a} 🝖 proof)

[⋅]-product-is-1ₗ : ∀{a b} → (a ⋅ b ≡ 1) → (a ≡ 1)
[⋅]-product-is-1ₗ {𝟎}   {_}   p = p
[⋅]-product-is-1ₗ {𝐒 a} {𝟎}   ()
[⋅]-product-is-1ₗ {𝐒 a} {𝐒 b} p = [≡]-with(𝐒) ([∧]-elimₗ ([+]-sum-is-0 (injective(𝐒) p)))

[⋅]-product-is-1ᵣ : ∀{a b} → (a ⋅ b ≡ 1) → (b ≡ 1)
[⋅]-product-is-1ᵣ {a}{b} = [⋅]-product-is-1ₗ {b}{a} ∘ (commutativity(_⋅_) {b}{a} 🝖_)

[⋅]-product-is-0 : ∀{a b} → (a ⋅ b ≡ 0) → ((a ≡ 0)∨(b ≡ 0))
[⋅]-product-is-0 {_}   {0}    _   = [∨]-introᵣ [≡]-intro
[⋅]-product-is-0 {0}   {𝐒(_)} _   = [∨]-introₗ [≡]-intro
[⋅]-product-is-0 {𝐒(a)}{𝐒(b)} ab0 with () ← [𝐒]-not-0 {(𝐒(a) ⋅ b) + a} (commutativity(_+_) {𝐒(a) ⋅ b}{𝐒(a)} 🝖 ab0)

[⋅]-product-is-positive : ∀{a b n} → (a ⋅ b ≡ 𝐒(n)) → (∃(n₁ ↦ a ≡ 𝐒(n₁)) ∧ ∃(n₂ ↦ b ≡ 𝐒(n₂)))
[⋅]-product-is-positive {_}   {0}    p with () ← [𝐒]-not-0 (symmetry(_≡_) p)
[⋅]-product-is-positive {0}   {𝐒(_)} p with () ← [𝐒]-not-0 (symmetry(_≡_) p)
[⋅]-product-is-positive {𝐒(a)}{𝐒(b)} p = [∧]-intro ([∃]-intro a) ([∃]-intro b)

instance
  [+]-cancellationᵣ : Cancellationᵣ(_+_)
  Cancellationᵣ.proof([+]-cancellationᵣ) {a}{x}{y} = ℕ-elim{T = \a → (x + a ≡ y + a) → (x ≡ y)} id (\_ → _∘ injective(𝐒)) a

instance
  [+]-cancellationₗ : Cancellationₗ(_+_)
  Cancellationₗ.proof([+]-cancellationₗ) {a}{x}{y} = cancellationᵣ(_+_) ∘ One.commuteBothTemp {a₁ = a}{x}{a}{y}

[^]-of-𝟎ₗ : ∀{x} → (𝟎 ^ 𝐒(x) ≡ 𝟎)
[^]-of-𝟎ₗ = [≡]-intro

[^]-of-𝟏ₗ : ∀{x} → (𝟏 ^ x ≡ 𝟏)
[^]-of-𝟏ₗ {𝟎}   = [≡]-intro
[^]-of-𝟏ₗ {𝐒 x} = [^]-of-𝟏ₗ {x}

[−₀]-absorberₗ-raw : ∀{x} → ((𝟎 −₀ x) ≡ 𝟎)
[−₀]-absorberₗ-raw {n} = ℕ-elim{T = \n → ((𝟎 −₀ n) ≡ 𝟎)} [≡]-intro (\_ _ → [≡]-intro) n
{-# REWRITE [−₀]-absorberₗ-raw #-}
instance
  [−₀]-absorberₗ : Absorberₗ (_−₀_) (𝟎)
  Absorberₗ.proof([−₀]-absorberₗ) {x} = [−₀]-absorberₗ-raw {x}

instance
  [−₀]-identityᵣ : Identityᵣ (_−₀_) (𝟎)
  Identityᵣ.proof([−₀]-identityᵣ) {x} = [≡]-intro

[−₀]-self : ∀{x} → ((x −₀ x) ≡ 𝟎)
[−₀]-self {n} = ℕ-elim{T = \n → ((n −₀ n) ≡ 𝟎)} [≡]-intro (\_ p → p) n
{-# REWRITE [−₀]-self #-}

[−₀]-with-[𝐒]ᵣ : ∀{x y} → ((x −₀ 𝐒(y)) ≡ 𝐏(x −₀ y))
[−₀]-with-[𝐒]ᵣ {𝟎} {𝟎}     = [≡]-intro
[−₀]-with-[𝐒]ᵣ {𝟎} {𝐒 y}   = [≡]-intro
[−₀]-with-[𝐒]ᵣ {𝐒 x} {𝟎}   = [≡]-intro
[−₀]-with-[𝐒]ᵣ {𝐒 x} {𝐒 y} = [−₀]-with-[𝐒]ᵣ {x} {y}

[−₀][−₀]-to-[−₀][+] : ∀{x y z} → ((x −₀ y) −₀ z ≡ x −₀ (y + z))
[−₀][−₀]-to-[−₀][+] {x}{y}{𝟎} = [≡]-intro
[−₀][−₀]-to-[−₀][+] {x}{y}{𝐒 z} =
  (x −₀ y) −₀ 𝐒(z) 🝖[ _≡_ ]-[ [−₀]-with-[𝐒]ᵣ {x −₀ y}{z} ]
  𝐏((x −₀ y) −₀ z) 🝖[ _≡_ ]-[ congruence₁(𝐏) ([−₀][−₀]-to-[−₀][+] {x}{y}{z}) ]
  𝐏(x −₀ (y + z))  🝖[ _≡_ ]-[ [−₀]-with-[𝐒]ᵣ {x}{y + z} ]-sym
  x −₀ 𝐒(y + z)    🝖[ _≡_ ]-[]
  x −₀ (y + 𝐒(z))  🝖-end

[−₀]ₗ[+]ᵣ-nullify : ∀{x y} → ((x + y) −₀ y ≡ x)
[−₀]ₗ[+]ᵣ-nullify{𝟎}   {𝟎}    = [≡]-intro
[−₀]ₗ[+]ᵣ-nullify{𝟎}   {𝐒(y)} = [≡]-intro
[−₀]ₗ[+]ᵣ-nullify{𝐒(x)}{𝐒(y)} = [≡]-intro 🝖 ([−₀]ₗ[+]ᵣ-nullify{𝐒(x)}{y})
[−₀]ₗ[+]ᵣ-nullify{𝐒(x)}{𝟎}    = [≡]-intro
instance
  [+][−₀]-inverseOperatorᵣ : InverseOperatorᵣ(_+_)(_−₀_)
  InverseOperatorᵣ.proof [+][−₀]-inverseOperatorᵣ {x} {y} = [−₀]ₗ[+]ᵣ-nullify {x}{y}

[−₀]ₗ[+]ₗ-nullify : ∀{x y} → ((x + y) −₀ x ≡ y)
[−₀]ₗ[+]ₗ-nullify {x}{y} = [≡]-substitutionᵣ (commutativity(_+_) {y}{x}) {expr ↦ (expr −₀ x ≡ y)} ([−₀]ₗ[+]ᵣ-nullify {y}{x})

[−₀][+]ᵣ-nullify : ∀{x₁ x₂ y} → ((x₁ + y) −₀ (x₂ + y) ≡ x₁ −₀ x₂)
[−₀][+]ᵣ-nullify {_} {_} {𝟎}    = [≡]-intro
[−₀][+]ᵣ-nullify {x₁}{x₂}{𝐒(y)} = [−₀][+]ᵣ-nullify {x₁}{x₂}{y}

[−₀][+]ₗ-nullify : ∀{x y₁ y₂} → ((x + y₁) −₀ (x + y₂) ≡ y₁ −₀ y₂)
[−₀][+]ₗ-nullify {x}{y₁}{y₂} =
  [≡]-with-op(_−₀_) (commutativity(_+_) {x}{y₁}) (commutativity(_+_) {x}{y₂})
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
... | [∨]-introₗ proof = [∨]-introₗ (commutativity(_+_) {y}{x −₀ y} 🝖 proof)
... | [∨]-introᵣ proof = [∨]-introᵣ proof

[𝄩]-𝐒-cases : ∀{x y} → (𝐒(x 𝄩 y) ≡ 𝐒(x) 𝄩 y) ∨ (𝐒(x 𝄩 y) ≡ x 𝄩 𝐒(y))
[𝄩]-𝐒-cases {𝟎}   {𝟎}   = [∨]-introₗ [≡]-intro
[𝄩]-𝐒-cases {𝟎}   {𝐒 y} = [∨]-introᵣ [≡]-intro
[𝄩]-𝐒-cases {𝐒 x} {𝟎}   = [∨]-introₗ [≡]-intro
[𝄩]-𝐒-cases {𝐒 x} {𝐒 y} = [𝄩]-𝐒-cases {x}{y}

[𝄩]-identityₗ-raw : Names.Identityₗ(_𝄩_)(0)
[𝄩]-identityₗ-raw {𝟎}    = [≡]-intro
[𝄩]-identityₗ-raw {𝐒(_)} = [≡]-intro
{-# REWRITE [𝄩]-identityₗ-raw #-}
instance
  [𝄩]-identityₗ : Identityₗ(_𝄩_)(𝟎)
  Identityₗ.proof([𝄩]-identityₗ) {x} = [𝄩]-identityₗ-raw {x}

[𝄩]-identityᵣ-raw : Names.Identityᵣ (_𝄩_) (0)
[𝄩]-identityᵣ-raw {𝟎}    = [≡]-intro
[𝄩]-identityᵣ-raw {𝐒(_)} = [≡]-intro
{-# REWRITE [𝄩]-identityᵣ-raw #-}
instance
  [𝄩]-identityᵣ : Identityᵣ(_𝄩_)(𝟎)
  Identityᵣ.proof([𝄩]-identityᵣ) {x} = [𝄩]-identityᵣ-raw {x}

instance
  [𝄩]-identity : Identity(_𝄩_)(𝟎)
  [𝄩]-identity = intro

[𝄩]-self : ∀{x} → (x 𝄩 x ≡ 𝟎)
[𝄩]-self {𝟎}    = [≡]-intro
[𝄩]-self {𝐒(x)} = [𝄩]-self {x}
{-# REWRITE [𝄩]-self #-}

instance
  [𝄩]-inverseFunctionₗ : InverseFunctionₗ(_𝄩_) ⦃ [∃]-intro 𝟎 ⦄ (id)
  [𝄩]-inverseFunctionₗ = intro \{x} → [𝄩]-self {x}

instance
  [𝄩]-inverseFunctionᵣ : InverseFunctionᵣ(_𝄩_) ⦃ [∃]-intro 𝟎 ⦄ (id)
  [𝄩]-inverseFunctionᵣ = intro \{x} → [𝄩]-self {x}

instance
  [𝄩]-commutativity : Commutativity(_𝄩_)
  Commutativity.proof([𝄩]-commutativity) {x}{y} = p{x}{y} where
    p : Names.Commutativity (_𝄩_)
    p{𝟎}   {𝟎}    = [≡]-intro
    p{𝟎}   {𝐒(y)} = [≡]-intro
    p{𝐒(x)}{𝟎}    = [≡]-intro
    p{𝐒(x)}{𝐒(y)} = p{x}{y}

instance
  [+][𝄩]-inverseOperatorᵣ : InverseOperatorᵣ(_+_)(_𝄩_)
  InverseOperatorᵣ.proof [+][𝄩]-inverseOperatorᵣ {x}{y} = p{x}{y} where
    p : ∀{x y} → ((x + y) 𝄩 y ≡ x)
    p{𝟎}   {𝟎}    = [≡]-intro
    p{𝟎}   {𝐒(y)} = [≡]-intro
    p{𝐒(x)}{𝐒(y)} = [≡]-intro 🝖 (p{𝐒(x)}{y})
    p{𝐒(x)}{𝟎}    = [≡]-intro

instance
  [swap+][𝄩]-inverseOperatorᵣ : InverseOperatorᵣ(swap(_+_))(_𝄩_)
  InverseOperatorᵣ.proof [swap+][𝄩]-inverseOperatorᵣ {x}{y} = congruence₂ₗ(_𝄩_)(y) (commutativity(_+_) {y}{x}) 🝖 inverseOperᵣ(_+_)(_𝄩_) {x}{y}

instance
  [swap+][𝄩]-inverseOperatorₗ : InverseOperatorₗ(swap(_+_))(_𝄩_)
  InverseOperatorₗ.proof [swap+][𝄩]-inverseOperatorₗ {x}{y} = commutativity(_𝄩_) {x}{y + x} 🝖 inverseOperᵣ(_+_)(_𝄩_) {y}{x}

instance
  [+][𝄩]-inverseOperatorₗ : InverseOperatorₗ(_+_)(_𝄩_)
  InverseOperatorₗ.proof [+][𝄩]-inverseOperatorₗ {x}{y} = commutativity(_𝄩_) {x}{x + y} 🝖 inverseOperᵣ(swap(_+_))(_𝄩_) {y}{x}

[𝄩]-with-[+]ᵣ : ∀{x y z} → ((x + z) 𝄩 (y + z) ≡ x 𝄩 y)
[𝄩]-with-[+]ᵣ {𝟎}   {𝟎}   {𝟎}    = [≡]-intro
[𝄩]-with-[+]ᵣ {𝟎}   {𝐒(y)}{𝟎}    = [≡]-intro
[𝄩]-with-[+]ᵣ {𝟎}   {𝟎}   {𝐒(z)} = [≡]-intro
[𝄩]-with-[+]ᵣ {𝟎}   {𝐒(y)}{𝐒(z)} = inverseOperₗ(swap(_+_))(_𝄩_) {z}{_}
[𝄩]-with-[+]ᵣ {𝐒(x)}{𝟎}   {𝟎}    = [≡]-intro
[𝄩]-with-[+]ᵣ {𝐒(x)}{𝐒(y)}{𝟎}    = [≡]-intro
[𝄩]-with-[+]ᵣ {𝐒(x)}{𝟎}   {𝐒(z)} = inverseOperᵣ(_+_)(_𝄩_) {𝐒(x)}{z}
[𝄩]-with-[+]ᵣ {𝐒(x)}{𝐒(y)}{𝐒(z)} = [𝄩]-with-[+]ᵣ {𝐒(x)}{𝐒(y)}{z}

[𝄩]-with-[+]ₗ : ∀{x y z} → ((z + x) 𝄩 (z + y) ≡ x 𝄩 y)
[𝄩]-with-[+]ₗ {𝟎}   {𝟎}   {𝟎}    = [≡]-intro
[𝄩]-with-[+]ₗ {𝟎}   {𝐒(y)}{𝟎}    = [≡]-intro
[𝄩]-with-[+]ₗ {𝟎}   {𝟎}   {𝐒(z)} = [≡]-intro
[𝄩]-with-[+]ₗ {𝟎}   {𝐒(y)}{𝐒(z)} = inverseOperₗ(_+_)(_𝄩_) {z}{𝐒(y)}
[𝄩]-with-[+]ₗ {𝐒(x)}{𝟎}   {𝟎}    = [≡]-intro
[𝄩]-with-[+]ₗ {𝐒(x)}{𝐒(y)}{𝟎}    = [≡]-intro
[𝄩]-with-[+]ₗ {𝐒(x)}{𝟎}   {𝐒(z)} = inverseOperᵣ(swap(_+_))(_𝄩_) {𝐒(x)}{z}
[𝄩]-with-[+]ₗ {𝐒(x)}{𝐒(y)}{𝐒(z)} = [𝄩]-with-[+]ₗ {𝐒(x)}{𝐒(y)}{z}

[𝄩]-equality : ∀{x y} → (x 𝄩 y ≡ 𝟎) → (x ≡ y)
[𝄩]-equality {𝟎}   {𝟎}    [≡]-intro = [≡]-intro
[𝄩]-equality {𝟎}   {𝐒(y)} ()
[𝄩]-equality {𝐒(x)}{𝟎}    ()
[𝄩]-equality {𝐒(x)}{𝐒(y)} proof     = [≡]-with(𝐒) ([𝄩]-equality {x}{y} proof)

instance
  [⋅][𝄩]-distributivityᵣ : Distributivityᵣ(_⋅_)(_𝄩_)
  Distributivityᵣ.proof [⋅][𝄩]-distributivityᵣ {x}{y}{z} = p{x}{y}{z} where
    p : Names.Distributivityᵣ(_⋅_)(_𝄩_)
    p {𝟎} {𝟎} {z} = [≡]-intro
    p {𝟎} {𝐒 y} {z} = [≡]-intro
    p {𝐒 x} {𝟎} {z} = [≡]-intro
    p {𝐒 x} {𝐒 y} {z} =
      (𝐒(x) 𝄩 𝐒(y)) ⋅ z             🝖[ _≡_ ]-[]
      (x 𝄩 y) ⋅ z                   🝖[ _≡_ ]-[ p{x}{y}{z} ]
      (x ⋅ z) 𝄩 (y ⋅ z)             🝖[ _≡_ ]-[ [𝄩]-with-[+]ᵣ {x ⋅ z}{y ⋅ z}{z} ]-sym
      ((x ⋅ z) + z) 𝄩 ((y ⋅ z) + z) 🝖[ _≡_ ]-[ congruence₂(_𝄩_) ([⋅]-with-[𝐒]ₗ {x}{z}) ([⋅]-with-[𝐒]ₗ {y}{z}) ]-sym
      (𝐒(x) ⋅ z) 𝄩 (𝐒(y) ⋅ z)       🝖-end

instance
  [⋅][𝄩]-distributivityₗ : Distributivityₗ(_⋅_)(_𝄩_)
  Distributivityₗ.proof [⋅][𝄩]-distributivityₗ {x}{y}{z} =
    x ⋅ (y 𝄩 z)       🝖[ _≡_ ]-[ commutativity(_⋅_) {x}{y 𝄩 z} ]
    (y 𝄩 z) ⋅ x       🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(_𝄩_) {y}{z}{x} ]
    (y ⋅ x) 𝄩 (z ⋅ x) 🝖[ _≡_ ]-[ congruence₂(_𝄩_) (commutativity(_⋅_) {y}{x}) (commutativity(_⋅_) {z}{x}) ]
    (x ⋅ y) 𝄩 (x ⋅ z) 🝖-end
