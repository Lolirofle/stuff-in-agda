module Numeral.Natural.Oper.Proofs.Order where

open import Data
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Classical
open import Numeral.Natural.Relation.Order.Proofs
open import Numeral.Natural.Relation.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Relator.Ordering.Proofs
open import Structure.Function.Domain
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

[≤]ₗ[+] : ∀{x y : ℕ} → (x + y ≤ x) → (y ≡ 𝟎)
[≤]ₗ[+] {𝟎}               = [≤][0]ᵣ
[≤]ₗ[+] {𝐒(x)}{y} (proof) = [≤]ₗ[+] {x} ([≤]-without-[𝐒] {x + y} {x} (proof))

[≤]-with-[+]ᵣ : ∀{x y z : ℕ} → (x ≤ y) → (x + z ≤ y + z)
[≤]-with-[+]ᵣ {_}{_}{𝟎}    (proof)    = proof
[≤]-with-[+]ᵣ {_}{_}{𝐒(z)} (proof) = [≤]-with-[𝐒] ⦃ [≤]-with-[+]ᵣ {_}{_}{z} (proof) ⦄

[≤]-with-[+]ₗ : ∀{x y z : ℕ} → (x ≤ y) → (z + x ≤ z + y)
[≤]-with-[+]ₗ {.0} {𝟎}   {z } min        = reflexivity(_≤_)
[≤]-with-[+]ₗ {.0} {𝐒 y} {z}  min        = [≤]-successor([≤]-with-[+]ₗ {0}{y}{z} [≤]-minimum)
[≤]-with-[+]ₗ {𝐒 x} {𝐒 y} {z} (succ xy ) = [≤]-with-[𝐒] ⦃ [≤]-with-[+]ₗ {x} {y} {z} xy ⦄

[≤]-of-[+]ᵣ : ∀{x y : ℕ} → (y ≤ x + y)
[≤]-of-[+]ᵣ {x}   {𝟎}   = [≤]-minimum
[≤]-of-[+]ᵣ {𝟎}   {𝐒 x} = reflexivity(_≤_)
[≤]-of-[+]ᵣ {𝐒 x} {𝐒 y} = [≤]-with-[𝐒] ⦃ [≤]-of-[+]ᵣ {𝐒 x}{y} ⦄

[≤]-of-[+]ₗ : ∀{x y : ℕ} → (x ≤ x + y)
[≤]-of-[+]ₗ {𝟎}   {y}   = [≤]-minimum
[≤]-of-[+]ₗ {𝐒 x} {𝟎}   = reflexivity(_≤_)
[≤]-of-[+]ₗ {𝐒 x} {𝐒 y} = [≤]-with-[𝐒] ⦃ [≤]-of-[+]ₗ {x}{𝐒 y} ⦄

[≤]-with-[+] : ∀{x₁ y₁ : ℕ} → ⦃ _ : (x₁ ≤ y₁)⦄ → ∀{x₂ y₂ : ℕ} → ⦃ _ : (x₂ ≤ y₂)⦄ → (x₁ + x₂ ≤ y₁ + y₂)
[≤]-with-[+] {x₁} {y₁} ⦃ x1y1 ⦄ {.0}   {y₂}   ⦃ min ⦄   = transitivity(_≤_) x1y1 [≤]-of-[+]ₗ
[≤]-with-[+] {x₁} {y₁} ⦃ x1y1 ⦄ {𝐒 x₂} {𝐒 y₂} ⦃ succ p ⦄ = succ ([≤]-with-[+] {x₁} {y₁} {x₂} {y₂} ⦃ p ⦄)

[≤]-from-[+] : ∀{ℓ}{P : ℕ → Stmt{ℓ}}{x} → (∀{n} → P(x + n)) → (∀{y} → ⦃ _ : (x ≤ y) ⦄ → P(y))
[≤]-from-[+] {ℓ} {P} {𝟎}   anpxn {y}   ⦃ [≤]-minimum ⦄        = anpxn{y}
[≤]-from-[+] {ℓ} {P} {𝐒 x} anpxn {𝐒 y} ⦃ succ xy ⦄ = [≤]-from-[+] {ℓ} {P ∘ 𝐒} {x} anpxn {y} ⦃ xy ⦄

[−₀][+]-nullify2 : ∀{x y} → (x ≤ y) ↔ (x + (y −₀ x) ≡ y)
[−₀][+]-nullify2 {x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
  l : ∀{x y} → (x ≤ y) ← (x + (y −₀ x) ≡ y)
  l {𝟎}   {_}    _     = [≤]-minimum
  l {𝐒(_)}{𝟎}    ()
  l {𝐒(x)}{𝐒(y)} proof = [≤]-with-[𝐒] ⦃ l{x}{y} (injective(𝐒) proof) ⦄

  r : ∀{x y} → (x ≤ y) → (x + (y −₀ x) ≡ y)
  r {𝟎}   {𝟎}    proof = [≡]-intro
  r {𝟎}   {𝐒(_)} proof = [≡]-intro
  r {𝐒(_)}{𝟎}    ()
  r {𝐒(x)}{𝐒(y)} (succ proof) = [≡]-with(𝐒) (r{x}{y} (proof))

[−₀][+]-nullify2ᵣ : ∀{x y} → (x ≤ y) ↔ ((y −₀ x) + x ≡ y)
[−₀][+]-nullify2ᵣ {x}{y} = [↔]-transitivity [−₀][+]-nullify2 ([≡]-substitution (commutativity(_+_) {x}{y −₀ x}) {_≡ y})

[−₀]-when-0 : ∀{x y} → (x ≤ y) ↔ (x −₀ y ≡ 𝟎)
[−₀]-when-0 {x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
  l : ∀{x y} → (x ≤ y) ← (x −₀ y ≡ 𝟎)
  l {𝟎}   {_}    _     = [≤]-minimum
  l {𝐒(_)}{𝟎}    ()
  l {𝐒(x)}{𝐒(y)} proof = [≤]-with-[𝐒] ⦃ l{x}{y} proof ⦄

  r : ∀{x y} → (x ≤ y) → (x −₀ y ≡ 𝟎)
  r {𝟎}   {_}    proof = [≡]-intro
  r {𝐒(_)}{𝟎}    ()
  r {𝐒(x)}{𝐒(y)} (succ proof) = r{x}{y} (proof)

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

[−₀][𝐒]ₗ-equality : ∀{x y} → (x ≥ y) ↔ ((𝐒(x) −₀ y) ≡ 𝐒(x −₀ y))
[−₀][𝐒]ₗ-equality = [↔]-intro l r where
  l : ∀{x y} → (x ≥ y) ← ((𝐒(x) −₀ y) ≡ 𝐒(x −₀ y))
  l {𝟎}   {𝟎}   p = [≤]-minimum
  l {𝐒 x} {𝟎}   p = [≤]-minimum
  l {𝐒 x} {𝐒 y} p = [≤]-with-[𝐒] ⦃ l{x}{y} p ⦄

  r : ∀{x y} → (x ≥ y) → ((𝐒(x) −₀ y) ≡ 𝐒(x −₀ y))
  r {x}   {.𝟎}  min       = [≡]-intro
  r {𝐒 x} {𝐒 y} (succ xy) = r xy

[−₀]-lesser : ∀{x y} → ((x −₀ y) ≤ x)
[−₀]-lesser {𝟎}   {_}    = [≤]-minimum
[−₀]-lesser {𝐒(x)}{𝟎}    = reflexivity(_≤_)
[−₀]-lesser {𝐒(x)}{𝐒(y)} = ([−₀]-lesser-[𝐒]ₗ {𝐒(x)}{y}) 🝖 ([−₀]-lesser {𝐒(x)}{y})

[−₀]-strictly-lesser : ∀{x y} ⦃ pos-y : Positive(y) ⦄ → (x ≥ y) → ((x −₀ y) < x)
[−₀]-strictly-lesser {.(𝐒 y)} {.(𝐒 x)} (succ {x} {y} xy) = succ ([−₀]-lesser {y}{x})

[≤][−₀]ₗ-preserving : ∀{a₁ a₂ b} → (a₁ ≤ a₂) → (a₁ −₀ b ≤ a₂ −₀ b)
[≤][−₀]ₗ-preserving {b = 𝟎}   ord        = ord
[≤][−₀]ₗ-preserving {b = 𝐒 _} min        = min
[≤][−₀]ₗ-preserving {b = 𝐒 b} (succ ord) = [≤][−₀]ₗ-preserving {b = b} ord

[≤][−₀]ᵣ-antipreserving : ∀{a b₁ b₂} → (b₁ ≥ b₂) → (a −₀ b₁ ≤ a −₀ b₂)
[≤][−₀]ᵣ-antipreserving {a}   {b₁}     {.𝟎}     min       = [−₀]-lesser {a}{b₁}
[≤][−₀]ᵣ-antipreserving {𝟎}   {.(𝐒 _)} {.(𝐒 _)} (succ pb) = min
[≤][−₀]ᵣ-antipreserving {𝐒 a} {.(𝐒 _)} {.(𝐒 _)} (succ pb) = [≤][−₀]ᵣ-antipreserving {a} pb

[<][−₀]ₗ-preserving : ∀{a₁ a₂ b} → (b ≤ a₁) → (a₁ < a₂) → (a₁ −₀ b < a₂ −₀ b)
[<][−₀]ₗ-preserving {b = 𝟎}   ord1        (succ ord2) = succ ord2
[<][−₀]ₗ-preserving {b = 𝐒 b} (succ ord1) (succ ord2) = [<][−₀]ₗ-preserving {b = b} ord1 ord2

[≤][−₀]ₗ-preserving-converse : ∀{a₁ a₂ b} → (a₁ ≥ b) → (a₂ ≥ b) → (a₁ −₀ b ≤ a₂ −₀ b) → (a₁ ≤ a₂)
[≤][−₀]ₗ-preserving-converse {𝟎}    {a₂}   {𝟎}   a1b        a2b        ord = min
[≤][−₀]ₗ-preserving-converse {𝐒 a₁} {𝐒 a₂} {𝟎}   a1b        a2b        ord = ord
[≤][−₀]ₗ-preserving-converse {𝐒 a₁} {𝐒 a₂} {𝐒 b} (succ a1b) (succ a2b) ord = succ ([≤][−₀]ₗ-preserving-converse {a₁} {a₂} {b} a1b a2b ord)

[<][−₀]ₗ-preserving-converse : ∀{a₁ a₂ b} → (a₁ ≥ b) → (a₂ ≥ b) → (a₁ −₀ b < a₂ −₀ b) → (a₁ < a₂)
[<][−₀]ₗ-preserving-converse {𝐒 a₁} {𝐒 a₂} {𝐒 b} (succ a1b) (succ a2b) ord = succ ([<][−₀]ₗ-preserving-converse {a₁} {a₂} {b} a1b a2b ord)
{-# CATCHALL #-}
[<][−₀]ₗ-preserving-converse {a₁}   {𝐒 a₂} {𝟎}   a1b        a2b        ord = ord

[≤][+]ᵣ-same : ∀{a₁ a₂ b c} → (a₁ + b ≤ a₂ + b) → (a₁ + c ≤ a₂ + c)
[≤][+]ᵣ-same {a₁} {a₂} {b}   {𝐒 c} ord        = succ([≤][+]ᵣ-same{a₁}{a₂}{b}{c} ord)
[≤][+]ᵣ-same {a₁} {a₂} {𝟎}   {𝟎}   ord        = ord
[≤][+]ᵣ-same {a₁} {a₂} {𝐒 b} {𝟎}   (succ ord) = [≤][+]ᵣ-same{a₁}{a₂}{b}{𝟎} ord

[≤][+]ₗ-same : ∀{a b c₁ c₂} → (a + c₁ ≤ a + c₂) → (b + c₁ ≤ b + c₂)
[≤][+]ₗ-same {a}{b}{c₁}{c₂} ord = substitute₂(_≤_) (commutativity(_+_) {c₁}{b}) (commutativity(_+_) {c₂}{b}) ([≤][+]ᵣ-same {c₁}{c₂}{a}{b} (substitute₂(_≤_) (commutativity(_+_) {a}{c₁}) (commutativity(_+_) {a}{c₂}) ord))

[<][+]ᵣ-same : ∀{a₁ a₂ b c} → (a₁ + b < a₂ + b) → (a₁ + c < a₂ + c)
[<][+]ᵣ-same {a₁}{a₂}{b}{c} = [≤][+]ᵣ-same {𝐒 a₁}{a₂}{b}{c}

[<][+]ₗ-same : ∀{a b c₁ c₂} → (a + c₁ < a + c₂) → (b + c₁ < b + c₂)
[<][+]ₗ-same {a}{b}{c₁}{c₂} = [≤][+]ₗ-same {a}{b}{𝐒 c₁}{c₂}

-- TODO: Converse is probably also true. One way to prove the equivalence is contraposition of [−₀]-comparison. Another is by [≤]-with-[+]ᵣ and some other stuff, but it seems to require more work. Also, this is [−₀]-positive
[<][−₀]-transfer : ∀{x y} → (y > x) → (y −₀ x > 0)
[<][−₀]-transfer {𝟎}   {𝐒(y)} _        = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄
[<][−₀]-transfer {𝐒(x)}{𝐒(y)} (succ p) = [<][−₀]-transfer {x}{y} p

[−₀]-positive : ∀{x y} → (y > x) ↔ Positive(y −₀ x)
[−₀]-positive = [↔]-intro l r where
  l : ∀{x y} → (y > x) ← Positive(y −₀ x)
  l {𝟎}   {𝐒 y} pos = succ min
  l {𝐒 x} {𝐒 y} pos = succ(l{x}{y} pos)

  r : ∀{x y} → (y > x) → Positive(y −₀ x)
  r{𝟎}   (succ {y = y} yx) = <>
  r{𝐒 x} (succ {y = y} yx) = r yx

[−₀]-nested-sameₗ : ∀{x y} → (x ≥ y) ↔ (x −₀ (x −₀ y) ≡ y)
[−₀]-nested-sameₗ {x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
  l : ∀{x y} → (x ≥ y) ← (x −₀ (x −₀ y) ≡ y)
  l {x}{y} proof =
    y             🝖[ _≤_ ]-[ [≡]-to-[≤] (symmetry(_≡_) proof) ]
    x −₀ (x −₀ y) 🝖[ _≤_ ]-[ [−₀]-lesser {x}{x −₀ y} ]
    x             🝖[ _≤_ ]-end

  r : ∀{x y} → (x ≥ y) → (x −₀ (x −₀ y) ≡ y)
  r{x}{y} x≥y =
    x −₀ (x −₀ y)              🝖[ _≡_ ]-[ [≡]-with(_−₀ (x −₀ y)) (symmetry(_≡_) ([↔]-to-[→] ([−₀][+]-nullify2 {y}{x}) (x≥y)) 🝖 commutativity(_+_) {y}{x −₀ y}) ]
    ((x −₀ y) + y) −₀ (x −₀ y) 🝖[ _≡_ ]-[ [−₀]ₗ[+]ₗ-nullify {x −₀ y}{y} ]
    y                          🝖-end

[+][−₀]-almost-associativity : ∀{x y z} → (y ≥ z) → ((x + y) −₀ z ≡ x + (y −₀ z))
[+][−₀]-almost-associativity {x} {y}   {.𝟎}  min      = [≡]-intro
[+][−₀]-almost-associativity {x} {𝐒 y} {𝐒 z} (succ p) = [+][−₀]-almost-associativity {x}{y}{z} p

[+][−₀]-almost-associativityₗ : ∀{x y z} → (x ≥ z) → ((x + y) −₀ z ≡ (x −₀ z) + y)
[+][−₀]-almost-associativityₗ {x}   {y} {𝟎}   min      = [≡]-intro
[+][−₀]-almost-associativityₗ {𝐒 x} {y} {𝐒 z} (succ p) = [+][−₀]-almost-associativityₗ {x}{y}{z} p

[−₀][𝄩]-equality-condition : ∀{x y} → (x ≥ y) ↔ (x −₀ y ≡ x 𝄩 y)
[−₀][𝄩]-equality-condition = [↔]-intro l r where
  l : ∀{x y} → (x ≥ y) ← (x −₀ y ≡ x 𝄩 y)
  l {_}   {𝟎}   _ = min
  l {𝐒 x} {𝐒 y} p = succ(l p)

  r : ∀{x y} → (x ≥ y) → (x −₀ y ≡ x 𝄩 y)
  r min = [≡]-intro
  r (succ p) = r p

[𝄩]-intro-by[−₀] : ∀{ℓ} (P : ℕ → Type{ℓ}) → ∀{x y} → P(x −₀ y) → P(y −₀ x) → P(x 𝄩 y)
[𝄩]-intro-by[−₀] _ {x = x}{y = y} p1 p2 with [≤][>]-dichotomy {x}{y}
... | [∨]-introₗ le
  rewrite [↔]-to-[→] [−₀][𝄩]-equality-condition le
  rewrite commutativity(_𝄩_) {x}{y}
  = p2
... | [∨]-introᵣ gt
  rewrite [↔]-to-[→] [−₀][𝄩]-equality-condition ([≤]-predecessor gt)
  = p1

[𝄩]-lesser : ∀{x y} → ((x 𝄩 y) ≤ x) ∨ ((x 𝄩 y) ≤ y)
[𝄩]-lesser {x}{y} = [𝄩]-intro-by[−₀] (d ↦ (d ≤ x) ∨ (d ≤ y)) {x}{y} ([∨]-introₗ ([−₀]-lesser {x}{y})) ([∨]-introᵣ ([−₀]-lesser {y}{x}))

[𝄩]-of-𝐒ₗ : ∀{x y} → (x ≥ y) → (𝐒(x) 𝄩 y ≡ 𝐒(x 𝄩 y))
[𝄩]-of-𝐒ₗ {𝟎}   {𝟎}   = const [≡]-intro
[𝄩]-of-𝐒ₗ {𝐒 x} {𝟎}   = const [≡]-intro
[𝄩]-of-𝐒ₗ {𝐒 x} {𝐒 y} = [𝄩]-of-𝐒ₗ {x} {y} ∘ [≤]-without-[𝐒]

[𝄩]-of-𝐒ᵣ : ∀{x y} → (x ≤ y) → (x 𝄩 𝐒(y) ≡ 𝐒(x 𝄩 y))
[𝄩]-of-𝐒ᵣ {𝟎}   {𝟎}   = const [≡]-intro
[𝄩]-of-𝐒ᵣ {𝟎}   {𝐒 y} = const [≡]-intro
[𝄩]-of-𝐒ᵣ {𝐒 x} {𝐒 y} = [𝄩]-of-𝐒ᵣ {x} {y} ∘ [≤]-without-[𝐒]

[<]-with-[+]ᵣ : ∀{x y z} → (x < y) → (x + z < y + z)
[<]-with-[+]ᵣ = [≤]-with-[+]ᵣ

[<]-with-[+]ₗ : ∀{x y z} → (y < z) → (x + y < x + z)
[<]-with-[+]ₗ {x}{y}{z} = [≤]-with-[+]ₗ {𝐒 y}{z}{x}

[<]-with-[+]-weak : ∀{x₁ x₂ y₁ y₂} → ((x₁ ≤ x₂) ∧ (y₁ < y₂)) ∨ ((x₁ < x₂) ∧ (y₁ ≤ y₂)) → (x₁ + y₁ < x₂ + y₂)
[<]-with-[+]-weak ([∨]-introₗ ([∧]-intro x12 y12)) = [≤]-with-[+] ⦃ x12 ⦄ ⦃ y12 ⦄
[<]-with-[+]-weak ([∨]-introᵣ ([∧]-intro x12 y12)) = [≤]-with-[+] ⦃ x12 ⦄ ⦃ y12 ⦄

[<]-with-[+] : ∀{x₁ x₂ y₁ y₂} → (x₁ < x₂) → (y₁ < y₂) → (x₁ + y₁ < x₂ + y₂)
[<]-with-[+] x12 y12 = [≤]-predecessor ([≤]-with-[+] ⦃ x12 ⦄ ⦃ y12 ⦄)

[≤]-with-[⋅]ᵣ : ∀{a b c} → (a ≤ b) → ((a ⋅ c) ≤ (b ⋅ c))
[≤]-with-[⋅]ᵣ {c = 𝟎}   _  = [≤]-minimum
[≤]-with-[⋅]ᵣ {c = 𝐒 c} ab = [≤]-with-[+] ⦃ ab ⦄ ⦃ [≤]-with-[⋅]ᵣ {c = c} ab ⦄

[≤]-with-[⋅]ₗ : ∀{a b c} → (b ≤ c) → ((a ⋅ b) ≤ (a ⋅ c))
[≤]-with-[⋅]ₗ {a}{b}{c}
  rewrite commutativity(_⋅_) {a}{b}
  rewrite commutativity(_⋅_) {a}{c}
  = [≤]-with-[⋅]ᵣ {c = a}

[<]-with-[⋅]ᵣ : ∀{a b c} → (a < b) → ((a ⋅ 𝐒(c)) < (b ⋅ 𝐒(c)))
[<]-with-[⋅]ᵣ {c = 𝟎}   = id
[<]-with-[⋅]ᵣ {c = 𝐒 c} = [<]-with-[+] ∘ₛ [<]-with-[⋅]ᵣ {c = c}

[<]-with-[⋅]ₗ : ∀{a b c} → (b < c) → ((𝐒(a) ⋅ b) < (𝐒(a) ⋅ c))
[<]-with-[⋅]ₗ {a}{b}{c}
  rewrite commutativity(_⋅_) {𝐒(a)}{b}
  rewrite commutativity(_⋅_) {𝐒(a)}{c}
  = [<]-with-[⋅]ᵣ {c = a}

[≤]-with-[⋅] : ∀{a₁ b₁ a₂ b₂} → (a₁ ≤ a₂) → (b₁ ≤ b₂) → ((a₁ ⋅ b₁) ≤ (a₂ ⋅ b₂))
[≤]-with-[⋅] {a₁}{b₁}{a₂}{b₂} ab1 ab2 = [≤]-with-[⋅]ₗ {a = a₁} ab2 🝖 [≤]-with-[⋅]ᵣ {c = b₂} ab1

[≤]-with-[−₀]ₗ : ∀{x₁ x₂ y} → (x₁ ≤ x₂) → (x₁ −₀ y ≤ x₂ −₀ y)
[≤]-with-[−₀]ₗ {y = _}   min       = min
[≤]-with-[−₀]ₗ {y = 𝟎}   (succ px) = succ px
[≤]-with-[−₀]ₗ {y = 𝐒 y} (succ px) = [≤]-with-[−₀]ₗ {y = y} px

[⋅]ᵣ-growing : ∀{n c} → (1 ≤ c) → (n ≤ (c ⋅ n))
[⋅]ᵣ-growing {n}{𝐒 c} = [≤]-with-[⋅]ᵣ {1}{𝐒(c)}{n}

[⋅]ᵣ-strictly-growing : ∀{n c} → (2 ≤ c) → (𝐒(n) < (c ⋅ 𝐒(n)))
[⋅]ᵣ-strictly-growing {n} {1} (succ())
[⋅]ᵣ-strictly-growing {n} {𝐒(𝐒 c)} = [<]-with-[⋅]ᵣ {1}{𝐒(𝐒(c))}{n}

[⋅]ₗ-growing : ∀{n c} → (1 ≤ c) → (n ≤ (n ⋅ c))
[⋅]ₗ-growing {n}{𝐒 c} = [≤]-with-[⋅]ₗ {n}{1}{𝐒(c)}

[⋅]ₗ-strictly-growing : ∀{n c} → (2 ≤ c) → (𝐒(n) < (𝐒(n) ⋅ c))
[⋅]ₗ-strictly-growing {n} {1} (succ())
[⋅]ₗ-strictly-growing {n} {𝐒(𝐒 c)} = [<]-with-[⋅]ₗ {n}{1}{𝐒(𝐒(c))}

[^]ₗ-strictly-growing : ∀{n a b} → (a < b) → ((𝐒(𝐒(n)) ^ a) < (𝐒(𝐒(n)) ^ b))
[^]ₗ-strictly-growing {n} {𝟎}   {.(𝐒 b)} (succ {y = b} p) = [≤]-with-[+]ᵣ [≤]-minimum 🝖 [≤]-with-[⋅]ₗ {𝐒(𝐒(n))}{1}{𝐒(𝐒(n)) ^ b} ([↔]-to-[→] Positive-greater-than-zero ([^]-positive {𝐒(𝐒(n))}{b}))
[^]ₗ-strictly-growing {n} {𝐒 a} {.(𝐒 b)} (succ {y = b} p) = [<]-with-[⋅]ₗ {𝐒(n)} ([^]ₗ-strictly-growing {n}{a}{b} p)

[^]ₗ-growing : ∀{n a b} → ¬((n ≡ 𝟎) ∧ (a ≡ 𝟎)) → (a ≤ b) → ((n ^ a) ≤ (n ^ b))
[^]ₗ-growing {𝟎}  {𝟎}   {_}   p _ with () ← p([∧]-intro [≡]-intro [≡]-intro)
[^]ₗ-growing {𝟎}  {𝐒 a} {𝐒 b} _ _ = min
[^]ₗ-growing {𝐒 𝟎}{a}   {b}   _ _
  rewrite [^]-of-𝟏ₗ {a}
  rewrite [^]-of-𝟏ₗ {b}
  = succ min
[^]ₗ-growing {𝐒 (𝐒 n)}{a}{b} _ ab with [≤]-to-[<][≡] ab
... | [∨]-introₗ p         = sub₂(_<_)(_≤_) ([^]ₗ-strictly-growing {n}{a}{b} p)
... | [∨]-introᵣ [≡]-intro = reflexivity(_≤_)

[≤]-of-[!] : ∀{n} → (1 ≤ (n !))
[≤]-of-[!] {𝟎}   = succ min
[≤]-of-[!] {𝐒 n} = [≤]-with-[⋅] {1}{1}{𝐒(n)}{n !} (succ min) ([≤]-of-[!] {n})

[<]-of-[+]ₗ : ∀{x y} ⦃ pos : Positive(y) ⦄ → (x < x + y)
[<]-of-[+]ₗ {y = 𝐒 y} = succ [≤]-of-[+]ₗ
