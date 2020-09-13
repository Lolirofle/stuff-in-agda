module Numeral.Natural.Oper.Proofs.Order where

open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Relator.Ordering.Proofs
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity

{-
[+][−₀]-commutativity : ∀{x y} → ⦃ _ : y ≥ z ⦄ → (x + (y −₀ z) ≡ (x −₀ z) + y)
-}

[≤]ₗ[+] : ∀{x y : ℕ} → (x + y ≤ x) → (y ≡ 𝟎)
[≤]ₗ[+] {𝟎}               = [≤][0]ᵣ
[≤]ₗ[+] {𝐒(x)}{y} (proof) = [≤]ₗ[+] {x} ([≤]-without-[𝐒] {x + y} {x} (proof))

[≤]-with-[+]ᵣ : ∀{x y z : ℕ} → (x ≤ y) → (x + z ≤ y + z)
[≤]-with-[+]ᵣ {_}{_}{𝟎}    (proof)    = proof
[≤]-with-[+]ᵣ {_}{_}{𝐒(z)} (proof) = [≤]-with-[𝐒] ⦃ [≤]-with-[+]ᵣ {_}{_}{z} (proof) ⦄

[≤]-with-[+]ₗ : ∀{x y z : ℕ} → (x ≤ y) → (z + x ≤ z + y)
[≤]-with-[+]ₗ {.0} {𝟎}   {z } [≤]-minimum            = reflexivity(_≤_)
[≤]-with-[+]ₗ {.0} {𝐒 y} {z}  [≤]-minimum            = [≤]-successor([≤]-with-[+]ₗ {0}{y}{z} [≤]-minimum)
[≤]-with-[+]ₗ {𝐒 x} {𝐒 y} {z} ([≤]-with-[𝐒] ⦃ xy ⦄ ) = [≤]-with-[𝐒] ⦃ [≤]-with-[+]ₗ {x} {y} {z} xy ⦄

[≤]-of-[+]ᵣ : ∀{x y : ℕ} → (y ≤ x + y)
[≤]-of-[+]ᵣ {x}   {𝟎}   = [≤]-minimum
[≤]-of-[+]ᵣ {𝟎}   {𝐒 x} = reflexivity(_≤_)
[≤]-of-[+]ᵣ {𝐒 x} {𝐒 y} = [≤]-with-[𝐒] ⦃ [≤]-of-[+]ᵣ {𝐒 x}{y} ⦄

[≤]-of-[+]ₗ : ∀{x y : ℕ} → (x ≤ x + y)
[≤]-of-[+]ₗ {𝟎}   {y}   = [≤]-minimum
[≤]-of-[+]ₗ {𝐒 x} {𝟎}   = reflexivity(_≤_)
[≤]-of-[+]ₗ {𝐒 x} {𝐒 y} =  [≤]-with-[𝐒] ⦃ [≤]-of-[+]ₗ {x}{𝐒 y} ⦄

[≤]-with-[+] : ∀{x₁ y₁ : ℕ} → ⦃ _ : (x₁ ≤ y₁)⦄ → ∀{x₂ y₂ : ℕ} → ⦃ _ : (x₂ ≤ y₂)⦄ → (x₁ + x₂ ≤ y₁ + y₂)
[≤]-with-[+] {x₁} {y₁} ⦃ x1y1 ⦄ {.0}     {y₂}     ⦃ [≤]-minimum ⦄ = transitivity(_≤_) x1y1 [≤]-of-[+]ₗ
[≤]-with-[+] {x₁} {y₁} ⦃ x1y1 ⦄ {𝐒 x₂} {𝐒 y₂} ⦃ [≤]-with-[𝐒] ⦃ p ⦄ ⦄ = [≤]-with-[𝐒] ⦃ [≤]-with-[+] {x₁} {y₁} {x₂} {y₂} ⦄

[≤]-from-[+] : ∀{ℓ}{P : ℕ → Stmt{ℓ}}{x} → (∀{n} → P(x + n)) → (∀{y} → ⦃ _ : (x ≤ y) ⦄ → P(y))
[≤]-from-[+] {ℓ} {P} {𝟎}   anpxn {y}   ⦃ [≤]-minimum ⦄        = anpxn{y}
[≤]-from-[+] {ℓ} {P} {𝐒 x} anpxn {𝐒 y} ⦃ [≤]-with-[𝐒] ⦃ xy ⦄ ⦄ = [≤]-from-[+] {ℓ} {P ∘ 𝐒} {x} anpxn {y} ⦃ xy ⦄

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
  r {𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = r{x}{y} (proof)

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
  r {x}   {.𝟎}  [≤]-minimum           = [≡]-intro
  r {𝐒 x} {𝐒 y} ([≤]-with-[𝐒] ⦃ xy ⦄) = r xy

[−₀]-lesser : ∀{x y} → ((x −₀ y) ≤ x)
[−₀]-lesser {𝟎}   {_}    = [≤]-minimum
[−₀]-lesser {𝐒(x)}{𝟎}    = reflexivity(_≤_)
[−₀]-lesser {𝐒(x)}{𝐒(y)} = ([−₀]-lesser-[𝐒]ₗ {𝐒(x)}{y}) 🝖 ([−₀]-lesser {𝐒(x)}{y})


-- TODO: Converse is probably also true. One way to prove the equivalence is contraposition of [−₀]-comparison. Another is by [≤]-with-[+]ᵣ and some other stuff, but it seems to require more work
[−₀]-positive : ∀{x y} → (y > x) → (y −₀ x > 0)
[−₀]-positive {𝟎}   {𝐒(y)} (_) = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄
[−₀]-positive {𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = [−₀]-positive {x}{y} (proof)

[−₀]-nested-sameₗ : ∀{x y} → (x ≥ y) ↔ (x −₀ (x −₀ y) ≡ y)
[−₀]-nested-sameₗ {x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
  l : ∀{x y} → (x ≥ y) ← (x −₀ (x −₀ y) ≡ y)
  l {x}{y} proof =
    y             🝖[ _≤_ ]-[ [≡]-to-[≤] (symmetry(_≡_) proof) ]
    x −₀ (x −₀ y) 🝖[ _≤_ ]-[ [−₀]-lesser {x}{x −₀ y} ]
    x             🝖[ _≤_ ]-end

  r : ∀{x y} → (x ≥ y) → (x −₀ (x −₀ y) ≡ y)
  r{x}{y} x≥y =
    x −₀ (x −₀ y)              🝖[ _≡_ ]-[ [≡]-with(_−₀ (x −₀ y)) (symmetry(_≡_) ([↔]-to-[→] ([−₀][+]-nullify2 {y}{x}) (x≥y)) 🝖 [+]-commutativity-raw{y}{x −₀ y}) ]
    ((x −₀ y) + y) −₀ (x −₀ y) 🝖[ _≡_ ]-[ [−₀]ₗ[+]ₗ-nullify {x −₀ y}{y} ]
    y                          🝖-end

[𝄩]-of-𝐒ₗ : ∀{x y} → (x ≥ y) → (𝐒(x) 𝄩 y ≡ 𝐒(x 𝄩 y))
[𝄩]-of-𝐒ₗ {𝟎}   {𝟎}   xy = [≡]-intro
[𝄩]-of-𝐒ₗ {𝐒 x} {𝟎}   xy = [≡]-intro
[𝄩]-of-𝐒ₗ {𝐒 x} {𝐒 y} xy = [𝄩]-of-𝐒ₗ {x} {y} ([≤]-without-[𝐒] xy)

[𝄩]-of-𝐒ᵣ : ∀{x y} → (x ≤ y) → (x 𝄩 𝐒(y) ≡ 𝐒(x 𝄩 y))
[𝄩]-of-𝐒ᵣ {𝟎}   {𝟎}   xy = [≡]-intro
[𝄩]-of-𝐒ᵣ {𝟎}   {𝐒 y} xy = [≡]-intro
[𝄩]-of-𝐒ᵣ {𝐒 x} {𝐒 y} xy = [𝄩]-of-𝐒ᵣ {x} {y} ([≤]-without-[𝐒] xy)

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
[≤]-with-[⋅]ᵣ {c = 𝟎} _ = [≤]-minimum
[≤]-with-[⋅]ᵣ {c = 𝐒 c} ab = [≤]-with-[+] ⦃ ab ⦄ ⦃ [≤]-with-[⋅]ᵣ {c = c} ab ⦄

[≤]-with-[⋅]ₗ : ∀{a b c} → (b ≤ c) → ((a ⋅ b) ≤ (a ⋅ c))
[≤]-with-[⋅]ₗ {a}{b}{c}
  rewrite commutativity(_⋅_) {a}{b}
  rewrite commutativity(_⋅_) {a}{c}
  = [≤]-with-[⋅]ᵣ {c = a}

[<]-with-[⋅]ᵣ : ∀{a b c} → (a < b) → ((a ⋅ 𝐒(c)) < (b ⋅ 𝐒(c)))
[<]-with-[⋅]ᵣ {c = 𝟎} ab = ab
[<]-with-[⋅]ᵣ {c = 𝐒 c} ab = [<]-with-[+] ab ([<]-with-[⋅]ᵣ {c = c} ab)

[<]-with-[⋅]ₗ : ∀{a b c} → (b < c) → ((𝐒(a) ⋅ b) < (𝐒(a) ⋅ c))
[<]-with-[⋅]ₗ {a}{b}{c}
  rewrite commutativity(_⋅_) {𝐒(a)}{b}
  rewrite commutativity(_⋅_) {𝐒(a)}{c}
  = [<]-with-[⋅]ᵣ {c = a}

[⋅]ᵣ-growing : ∀{n c} → (1 ≤ c) → (n ≤ (c ⋅ n))
[⋅]ᵣ-growing {n}{𝐒 c} = [≤]-with-[⋅]ᵣ {1}{𝐒(c)}{n}

[⋅]ᵣ-strictly-growing : ∀{n c} → (2 ≤ c) → (𝐒(n) < (c ⋅ 𝐒(n)))
[⋅]ᵣ-strictly-growing {n} {1} ([≤]-with-[𝐒] ⦃ ⦄)
[⋅]ᵣ-strictly-growing {n} {𝐒(𝐒 c)} = [<]-with-[⋅]ᵣ {1}{𝐒(𝐒(c))}{n}

[^]-positive : ∀{a b} → ((𝐒(a) ^ b) > 0)
[^]-positive {a}{𝟎} = reflexivity(_≤_)
[^]-positive {a}{𝐒 b} =
  𝐒(a) ^ 𝐒(b)       🝖[ _≥_ ]-[]
  𝐒(a) ⋅ (𝐒(a) ^ b) 🝖[ _≥_ ]-[ [<]-with-[⋅]ₗ {a} ([^]-positive {a}{b}) ]
  𝐒(𝐒(a) ⋅ 0)       🝖[ _≥_ ]-[ [≡]-to-[≤] ([≡]-with(𝐒) (reflexivity(_≡_))) ]
  1                 🝖[ _≥_ ]-end

[^]ₗ-strictly-growing : ∀{n a b} → (a < b) → ((𝐒(𝐒(n)) ^ a) < (𝐒(𝐒(n)) ^ b))
[^]ₗ-strictly-growing {n} {𝟎}   {.(𝐒 b)} ([≤]-with-[𝐒] {y = b} ⦃ p ⦄) = [≤]-with-[+]ᵣ [≤]-minimum 🝖 [≤]-with-[⋅]ₗ {𝐒(𝐒(n))}{1}{𝐒(𝐒(n)) ^ b} ([^]-positive {𝐒(n)}{b})
[^]ₗ-strictly-growing {n} {𝐒 a} {.(𝐒 b)} ([≤]-with-[𝐒] {y = b} ⦃ p ⦄) = [<]-with-[⋅]ₗ {𝐒(n)} ([^]ₗ-strictly-growing {n}{a}{b} p)

postulate [^]ₗ-growing : ∀{n a b} → (a ≤ b) → ((n ^ a) ≤ (n ^ b))
