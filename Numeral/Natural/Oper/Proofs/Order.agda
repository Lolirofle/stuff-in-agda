module Numeral.Natural.Oper.Proofs.Order where

open import Logic.Propositional
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
