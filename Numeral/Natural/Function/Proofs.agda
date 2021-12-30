module Numeral.Natural.Function.Proofs where

import      Lvl
open import Data.Tuple
open import Functional
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Logic.Propositional.Theorems
open import Numeral.Natural
open import Numeral.Natural.Function
open import Numeral.Natural.Relation.Order as ≤ using (_≤_ ; _≥_ ; _<_ ; _>_)
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Function.Domain
import      Structure.Operator.Names as Names
open import Structure.Operator.Proofs
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ : Lvl.Level

---------------------------------------------------------------------------------------------------
-- Min/max by 0

max-0ₗ : ∀{b} → (max 𝟎 b ≡ b)
max-0ₗ {𝟎}   = [≡]-intro
max-0ₗ {𝐒 b} = [≡]-intro
{-# REWRITE max-0ₗ #-}

max-0ᵣ : ∀{a} → (max a 𝟎 ≡ a)
max-0ᵣ {𝟎}   = [≡]-intro
max-0ᵣ {𝐒 a} = [≡]-intro
{-# REWRITE max-0ᵣ #-}

min-0ₗ : ∀{b} → (min 𝟎 b ≡ 𝟎)
min-0ₗ {𝟎}   = [≡]-intro
min-0ₗ {𝐒 b} = [≡]-intro
{-# REWRITE min-0ₗ #-}

min-0ᵣ : ∀{a} → (min a 𝟎 ≡ 𝟎)
min-0ᵣ {𝟎}   = [≡]-intro
min-0ᵣ {𝐒 a} = [≡]-intro
{-# REWRITE min-0ᵣ #-}

---------------------------------------------------------------------------------------------------
-- Proof methods for formulas including min/max

min-intro-by-strict-order : (P : {ℕ} → {ℕ} → ℕ → Type{ℓ}) → (∀{a b} → (a < b) → P{a}{b}(a)) → (∀{n} → P{n}{n}(n)) → (∀{a b} → (a > b) → P{a}{b}(b)) → (∀{a b} → P{a}{b}(min a b))
min-intro-by-strict-order P l e r {𝟎}   {𝟎}   = e
min-intro-by-strict-order P l e r {𝟎}   {𝐒 b} = l(_≤_.succ _≤_.min)
min-intro-by-strict-order P l e r {𝐒 a} {𝟎}   = r(_≤_.succ _≤_.min)
min-intro-by-strict-order P l e r {𝐒 a} {𝐒 b} = min-intro-by-strict-order(P ∘ 𝐒) (l ∘ _≤_.succ) e (r ∘ _≤_.succ)

max-intro-by-strict-order : (P : {ℕ} → {ℕ} → ℕ → Type{ℓ}) → (∀{a b} → (a > b) → P{a}{b}(a)) → (∀{n} → P{n}{n}(n)) → (∀{a b} → (a < b) → P{a}{b}(b)) → (∀{a b} → P{a}{b}(max a b))
max-intro-by-strict-order P l e r {𝟎}   {𝟎}   = e
max-intro-by-strict-order P l e r {𝟎}   {𝐒 b} = r(_≤_.succ _≤_.min)
max-intro-by-strict-order P l e r {𝐒 a} {𝟎}   = l(_≤_.succ _≤_.min)
max-intro-by-strict-order P l e r {𝐒 a} {𝐒 b} = max-intro-by-strict-order(P ∘ 𝐒) (l ∘ _≤_.succ) e (r ∘ _≤_.succ)

min-intro-by-weak-order : (P : {ℕ} → {ℕ} → ℕ → Type{ℓ}) → (∀{a b} → (a ≤ b) → P{a}{b}(a)) → (∀{a b} → (a ≥ b) → P{a}{b}(b)) → (∀{a b} → P{a}{b}(min a b))
min-intro-by-weak-order P l r = min-intro-by-strict-order P (l ∘ sub₂(_<_)(_≤_)) (l(reflexivity(_≤_))) (r ∘ sub₂(_<_)(_≤_))

max-intro-by-weak-order : (P : {ℕ} → {ℕ} → ℕ → Type{ℓ}) → (∀{a b} → (a ≥ b) → P{a}{b}(a)) → (∀{a b} → (a ≤ b) → P{a}{b}(b)) → (∀{a b} → P{a}{b}(max a b))
max-intro-by-weak-order P l r = max-intro-by-strict-order P (l ∘ sub₂(_<_)(_≤_)) (l(reflexivity(_≤_))) (r ∘ sub₂(_<_)(_≤_))

min-intro-by-weak-strict-order : (P : {ℕ} → {ℕ} → ℕ → Type{ℓ}) → (∀{a b} → (a ≤ b) → P{a}{b}(a)) → (∀{a b} → (a > b) → P{a}{b}(b)) → (∀{a b} → P{a}{b}(min a b))
min-intro-by-weak-strict-order P l r = min-intro-by-strict-order P (l ∘ sub₂(_<_)(_≤_)) (l(reflexivity(_≤_))) r

max-intro-by-weak-strict-order : (P : {ℕ} → {ℕ} → ℕ → Type{ℓ}) → (∀{a b} → (a ≥ b) → P{a}{b}(a)) → (∀{a b} → (a < b) → P{a}{b}(b)) → (∀{a b} → P{a}{b}(max a b))
max-intro-by-weak-strict-order P l r = max-intro-by-strict-order P (l ∘ sub₂(_<_)(_≤_)) (l(reflexivity(_≤_))) r

---------------------------------------------------------------------------------------------------
-- Proof related to min

instance
  min-idempotence : Idempotence(min)
  min-idempotence = intro proof where
    proof : Names.Idempotence(min)
    proof{𝟎}   = [≡]-intro
    proof{𝐒 x} = congruence₁(𝐒) (proof{x})

instance
  min-commutativity : Commutativity(min)
  Commutativity.proof(min-commutativity) = proof where
    proof : Names.Commutativity(min)
    proof{𝟎}   {𝟎}    = [≡]-intro
    proof{𝟎}   {𝐒(b)} = [≡]-intro
    proof{𝐒(a)}{𝟎}    = [≡]-intro
    proof{𝐒(a)}{𝐒(b)} = congruence₁(𝐒) (proof{a}{b})

instance
  min-associativity : Associativity(min)
  Associativity.proof(min-associativity) = proof where
    proof : Names.Associativity(min)
    proof{𝟎}   {𝟎}   {𝟎}    = [≡]-intro
    proof{𝟎}   {𝟎}   {𝐒(c)} = [≡]-intro
    proof{𝟎}   {𝐒(b)}{𝟎}    = [≡]-intro
    proof{𝐒(a)}{𝟎}   {𝟎}    = [≡]-intro
    proof{𝟎}   {𝐒(b)}{𝐒(c)} = [≡]-intro
    proof{𝐒(a)}{𝟎}   {𝐒(c)} = [≡]-intro
    proof{𝐒(a)}{𝐒(b)}{𝟎}    = [≡]-intro
    proof{𝐒(a)}{𝐒(b)}{𝐒(c)} = congruence₁(𝐒) (proof{a}{b}{c})

instance
  [+]-min-distributivityₗ : Distributivityₗ(_+_)(min)
  [+]-min-distributivityₗ = intro(\{x}{y}{z} → proof{x}{y}{z}) where
    proof : Names.Distributivityₗ(_+_)(min)
    proof {𝟎}   {y} {z} = [≡]-intro
    proof {𝐒 x} {y} {z} = congruence₁(𝐒) (proof{x}{y}{z})

instance
  [+]-min-distributivityᵣ : Distributivityᵣ(_+_)(min)
  [+]-min-distributivityᵣ = [↔]-to-[→] OneTypeTwoOp.distributivity-equivalence-by-commutativity [+]-min-distributivityₗ

min-elementary : ∀{a b} → (min(a)(b) ≡ b −₀ (b −₀ a))
min-elementary {𝟎}    {𝟎}    = [≡]-intro
min-elementary {𝟎}    {𝐒(b)} = [≡]-intro
min-elementary {𝐒(a)} {𝟎}    = [≡]-intro
min-elementary {𝐒(a)} {𝐒(b)} = (congruence₁(𝐒) (min-elementary {a} {b})) 🝖 (symmetry(_≡_) ([↔]-to-[→] [−₀][𝐒]ₗ-equality ([−₀]-lesser {b}{a})))

min-order : ∀{a b} → (min(a)(b) ≤ a) ∧ (min(a)(b) ≤ b)
min-order = [∧]-intro
  (min-intro-by-weak-order(\{a}{b} m → m ≤ a) (const(reflexivity(_≤_))) id)
  (min-intro-by-weak-order(\{a}{b} m → m ≤ b) id (const(reflexivity(_≤_))))

min-values : ∀{a b} → (min(a)(b) ≡ a) ∨ (min(a)(b) ≡ b)
min-values {𝟎}   {𝟎}    = [∨]-introₗ([≡]-intro)
min-values {𝟎}   {𝐒(b)} = [∨]-introₗ([≡]-intro)
min-values {𝐒(a)}{𝟎}    = [∨]-introᵣ([≡]-intro)
min-values {𝐒(a)}{𝐒(b)} = constructive-dilemma (congruence₁(𝐒)) (congruence₁(𝐒)) (min-values {a}{b})

min-defₗ : ∀{a b} → (a ≤ b) ↔ (min(a)(b) ≡ a)
min-defₗ = [↔]-intro
  (min-intro-by-weak-strict-order(\{a}{b} m → (a ≤ b) ← (m ≡ a)) const (const(sub₂(_≡_)(_≤_) ∘ symmetry(_≡_))))
  (min-intro-by-weak-order       (\{a}{b} m → (a ≤ b) → (m ≡ a)) (const(const(reflexivity(_≡_)))) (antisymmetry(_≤_)(_≡_)))

min-defᵣ : ∀{a b} → (b ≤ a) ↔ (min(a)(b) ≡ b)
min-defᵣ = min-defₗ 🝖 ([↔]-intro (commutativity(min) 🝖_) (commutativity(min) 🝖_))

[≤]-conjunction-min : ∀{a b c} → ((a ≤ b) ∧ (a ≤ c)) ↔ (a ≤ min b c)
[≤]-conjunction-min {a}{b}{c} = [↔]-intro
  (a≤bc ↦ [∧]-intro (a≤bc 🝖 [∧]-elimₗ min-order) (a≤bc 🝖 [∧]-elimᵣ min-order))
  (uncurry(min-intro-by-weak-order(\{b}{c} m → (_ ≤ b) → (_ ≤ c) → (_ ≤ m)) (const proj₂ₗ) (const proj₂ᵣ)))

[≤]-disjunction-min : ∀{a b c} → ((a ≤ c) ∨ (b ≤ c)) ↔ (min a b ≤ c)
[≤]-disjunction-min{c = c} = [↔]-intro
  (min-intro-by-weak-order(\{a}{b} m → ((a ≤ c) ∨ (b ≤ c)) ← (m ≤ c)) (const([∨]-introₗ)) (const([∨]-introᵣ)))
  (min-intro-by-weak-order(\{a}{b} m → ((a ≤ c) ∨ (b ≤ c)) → (m ≤ c)) ([∨]-elim id ∘ (_🝖_)) (Functional.swap [∨]-elim id ∘ (_🝖_)))

---------------------------------------------------------------------------------------------------
-- Proof related to max

instance
  max-idempotence : Idempotence(max)
  max-idempotence = intro proof where
    proof : Names.Idempotence(max)
    proof{𝟎}   = [≡]-intro
    proof{𝐒 x} = congruence₁(𝐒) (proof{x})

instance
  max-commutativity : Commutativity(max)
  Commutativity.proof(max-commutativity) = proof where
    proof : Names.Commutativity(max)
    proof{𝟎}   {𝟎}    = [≡]-intro
    proof{𝟎}   {𝐒(b)} = [≡]-intro
    proof{𝐒(a)}{𝟎}    = [≡]-intro
    proof{𝐒(a)}{𝐒(b)} = congruence₁(𝐒) (proof{a}{b})

instance
  max-associativity : Associativity(max)
  Associativity.proof(max-associativity) = proof where
    proof : Names.Associativity(max)
    proof{𝟎}   {𝟎}   {𝟎}    = [≡]-intro
    proof{𝟎}   {𝟎}   {𝐒(c)} = [≡]-intro
    proof{𝟎}   {𝐒(b)}{𝟎}    = [≡]-intro
    proof{𝐒(a)}{𝟎}   {𝟎}    = [≡]-intro
    proof{𝟎}   {𝐒(b)}{𝐒(c)} = [≡]-intro
    proof{𝐒(a)}{𝟎}   {𝐒(c)} = [≡]-intro
    proof{𝐒(a)}{𝐒(b)}{𝟎}    = [≡]-intro
    proof{𝐒(a)}{𝐒(b)}{𝐒(c)} = congruence₁(𝐒) (proof{a}{b}{c})

instance
  [+]-max-distributivityₗ : Distributivityₗ(_+_)(max)
  [+]-max-distributivityₗ = intro(\{x}{y}{z} → proof{x}{y}{z}) where
    proof : Names.Distributivityₗ(_+_)(max)
    proof {𝟎}   {y} {z} = [≡]-intro
    proof {𝐒 x} {y} {z} = congruence₁(𝐒) (proof{x}{y}{z})

instance
  [+]-max-distributivityᵣ : Distributivityᵣ(_+_)(max)
  [+]-max-distributivityᵣ = [↔]-to-[→] OneTypeTwoOp.distributivity-equivalence-by-commutativity [+]-max-distributivityₗ

max-elementary : ∀{a b} → (max(a)(b) ≡ a + (b −₀ a))
max-elementary {𝟎}    {𝟎}    = [≡]-intro
max-elementary {𝟎}    {𝐒(b)} = [≡]-intro
max-elementary {𝐒(a)} {𝟎}    = [≡]-intro
max-elementary {𝐒(a)} {𝐒(b)} = congruence₁(𝐒) (max-elementary {a} {b})

max-order : ∀{a b} → (max(a)(b) ≥ a) ∧ (max(a)(b) ≥ b)
max-order = [∧]-intro
  (max-intro-by-weak-order(\{a}{b} m → m ≥ a) (const(reflexivity(_≤_))) id)
  (max-intro-by-weak-order(\{a}{b} m → m ≥ b) id (const(reflexivity(_≤_))))

max-values : ∀{a b} → (max(a)(b) ≡ a) ∨ (max(a)(b) ≡ b)
max-values {𝟎}   {𝟎}    = [∨]-introₗ([≡]-intro)
max-values {𝟎}   {𝐒(b)} = [∨]-introᵣ([≡]-intro)
max-values {𝐒(a)}{𝟎}    = [∨]-introₗ([≡]-intro)
max-values {𝐒(a)}{𝐒(b)} = constructive-dilemma (congruence₁(𝐒)) (congruence₁(𝐒)) (max-values {a}{b})

max-defₗ : ∀{a b} → (a ≥ b) ↔ (max(a)(b) ≡ a)
max-defₗ {a}{b} = [↔]-intro
  (max-intro-by-weak-strict-order(\{a}{b} m → (a ≥ b) ← (m ≡ a)) const (const(sub₂(_≡_)(_≤_))))
  (max-intro-by-weak-order       (\{a}{b} m → (a ≥ b) → (m ≡ a)) (const(const(reflexivity(_≡_)))) (Functional.swap(antisymmetry(_≤_)(_≡_))))

max-defᵣ : ∀{a b} → (b ≥ a) ↔ (max(a)(b) ≡ b)
max-defᵣ = max-defₗ 🝖 ([↔]-intro (commutativity(max) 🝖_) (commutativity(max) 🝖_))

[≤]-conjunction-max : ∀{a b c} → ((a ≤ c) ∧ (b ≤ c)) ↔ (max a b ≤ c)
[≤]-conjunction-max {a}{b}{c} = [↔]-intro
  (ab≤c ↦ [∧]-intro ([∧]-elimₗ max-order 🝖 ab≤c) (([∧]-elimᵣ max-order 🝖 ab≤c)))
  (uncurry(max-intro-by-weak-order(\{a}{b} m → (a ≤ _) → (b ≤ _) → (m ≤ _)) (const proj₂ₗ) (const proj₂ᵣ)))

[≤]-disjunction-max : ∀{a b c} → ((a ≤ b) ∨ (a ≤ c)) ↔ (a ≤ max b c)
[≤]-disjunction-max{a = a} = [↔]-intro
  (max-intro-by-weak-order(\{b}{c} m → ((a ≤ b) ∨ (a ≤ c)) ← (a ≤ m)) (const([∨]-introₗ)) (const([∨]-introᵣ)))
  (max-intro-by-weak-order(\{b}{c} m → ((a ≤ b) ∨ (a ≤ c)) → (a ≤ m)) ([∨]-elim id ∘ (_🝖_)) (Functional.swap [∨]-elim id ∘ (_🝖_)))

max-order-[+] : ∀{a b} → (max(a)(b) ≤ a + b)
max-order-[+] {a}{b} = [↔]-to-[→] [≤]-conjunction-max ([∧]-intro [≤]-of-[+]ₗ ([≤]-of-[+]ᵣ {a}{b}))

---------------------------------------------------------------------------------------------------
-- Proof relating min and max

min-with-max : ∀{a b} → (min(a)(b) ≡ (a + b) −₀ max(a)(b))
min-with-max {a}{b} =
  min(a)(b)                 🝖-[ min-elementary{a}{b} ]
  b −₀ (b −₀ a)             🝖-[ [−₀][+]ₗ-nullify {a}{b}{b −₀ a} ]-sym
  (a + b) −₀ (a + (b −₀ a)) 🝖-[ congruence₁((a + b) −₀_) (max-elementary{a}{b}) ]-sym
  (a + b) −₀ max(a)(b)      🝖-end

max-with-min : ∀{a b} → (max(a)(b) ≡ (a + b) −₀ min(a)(b))
max-with-min {a}{b} with [≤][>]-dichotomy {a}{b}
... | [∨]-introₗ ab =
  max(a)(b)            🝖-[ [↔]-to-[→] max-defᵣ ab ]
  b                    🝖-[ [−₀]ₗ[+]ₗ-nullify {a}{b} ]-sym
  (a + b) −₀ a         🝖-[ congruence₁((a + b) −₀_) ([↔]-to-[→] min-defₗ ab) ]-sym
  (a + b) −₀ min(a)(b) 🝖-end
... | [∨]-introᵣ 𝐒ba with ba ← [≤]-predecessor 𝐒ba =
  max(a)(b)            🝖-[ [↔]-to-[→] max-defₗ ba ]
  a                    🝖-[ [−₀]ₗ[+]ᵣ-nullify {a}{b} ]-sym
  (a + b) −₀ b         🝖-[ congruence₁((a + b) −₀_) ([↔]-to-[→] min-defᵣ ba) ]-sym
  (a + b) −₀ min(a)(b) 🝖-end

min-order-max : ∀{a b} → (min(a)(b) ≤ max(a)(b))
min-order-max {𝟎}   {b}   = [≤]-minimum
min-order-max {𝐒 a} {𝟎}   = [≤]-minimum
min-order-max {𝐒 a} {𝐒 b} = [≤]-with-[𝐒] ⦃ min-order-max {a}{b} ⦄

min-when-max : ∀{a b} → (min(a)(b) ≡ a) ↔ (max(a)(b) ≡ b)
min-when-max {𝟎}   {_}   = [↔]-intro (const [≡]-intro) (const [≡]-intro)
min-when-max {𝐒 a} {𝟎}   = [↔]-intro (\()) (\())
min-when-max {𝐒 a} {𝐒 b} = [↔]-intro (congruence₁(𝐒)) (injective(𝐒)) 🝖 min-when-max {a}{b} 🝖 [↔]-intro (injective(𝐒)) (congruence₁(𝐒))

max-when-min : ∀{a b} → (max(a)(b) ≡ a) ↔ (min(a)(b) ≡ b)
max-when-min {_}   {𝟎}   = [↔]-intro (const [≡]-intro) (const [≡]-intro)
max-when-min {𝟎}   {𝐒 a} = [↔]-intro (\()) (\())
max-when-min {𝐒 a} {𝐒 b} = [↔]-intro (congruence₁(𝐒)) (injective(𝐒)) 🝖 max-when-min {a}{b} 🝖 [↔]-intro (injective(𝐒)) (congruence₁(𝐒))
