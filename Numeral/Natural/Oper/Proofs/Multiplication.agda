module Numeral.Natural.Oper.Proofs.Multiplication where

open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Classical
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Operator
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity

instance
  [⋅][−₀]-distributivityᵣ : Distributivityᵣ(_⋅_)(_−₀_)
  Distributivityᵣ.proof([⋅][−₀]-distributivityᵣ) {x}{y}{z} = p{x}{y}{z} where
    p : ∀{x y z : ℕ} → ((x −₀ y) ⋅ z) ≡ (x ⋅ z) −₀ (y ⋅ z)
    p {x} {y} {𝟎} = [≡]-intro
    p {x} {y} {𝐒 z} with [≥]-or-[<] {x}{y}
    ... | [∨]-introₗ gt =
      (x −₀ y) ⋅ 𝐒(z)                 🝖[ _≡_ ]-[]
      (x −₀ y) + ((x −₀ y) ⋅ z)       🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x −₀ y) (p {x}{y}{z}) ]
      (x −₀ y) + ((x ⋅ z) −₀ (y ⋅ z)) 🝖[ _≡_ ]-[ [+][−₀]-almost-associativity {x −₀ y} ([≤]-with-[⋅]ᵣ {c = z} gt) ]-sym
      ((x −₀ y) + (x ⋅ z)) −₀ (y ⋅ z) 🝖[ _≡_ ]-[ congruence₂ₗ(_−₀_)(y ⋅ z) (commutativity(_+_) {x −₀ y}{x ⋅ z}) ]
      ((x ⋅ z) + (x −₀ y)) −₀ (y ⋅ z) 🝖[ _≡_ ]-[ congruence₂ₗ(_−₀_)(y ⋅ z) ([+][−₀]-almost-associativity {x ⋅ z} gt) ]-sym
      (((x ⋅ z) + x) −₀ y) −₀ (y ⋅ z) 🝖[ _≡_ ]-[ congruence₂ₗ(_−₀_)(y ⋅ z) (congruence₂ₗ(_−₀_)(y) (commutativity(_+_) {x ⋅ z}{x})) ]
      ((x + (x ⋅ z)) −₀ y) −₀ (y ⋅ z) 🝖[ _≡_ ]-[ [−₀][−₀]-to-[−₀][+] {x + (x ⋅ z)}{y}{y ⋅ z} ]
      (x + (x ⋅ z)) −₀ (y + (y ⋅ z))  🝖[ _≡_ ]-[]
      (x ⋅ 𝐒(z)) −₀ (y ⋅ 𝐒(z))        🝖-end
    ... | [∨]-introᵣ lt =
      (x −₀ y) ⋅ 𝐒(z)                🝖[ _≡_ ]-[ congruence₂ₗ(_⋅_)(𝐒(z)) ([↔]-to-[→] [−₀]-when-0 (sub₂(_<_)(_≤_) lt)) ]
      𝟎 ⋅ 𝐒(z)                       🝖[ _≡_ ]-[ absorberₗ(_⋅_)(𝟎) {𝐒(z)} ]
      𝟎                              🝖[ _≡_ ]-[ [↔]-to-[→] [−₀]-when-0 ([≤]-with-[+] ⦃ sub₂(_<_)(_≤_) lt ⦄ ⦃ [≤]-with-[⋅]ᵣ {c = z} (sub₂(_<_)(_≤_) lt) ⦄) ]-sym
      (x + (x ⋅ z)) −₀ (y + (y ⋅ z)) 🝖-end

-- TODO: This is a specialized distributivity-equivalence-by-commutativity
instance
  [⋅][−₀]-distributivityₗ : Distributivityₗ(_⋅_)(_−₀_)
  Distributivityₗ.proof([⋅][−₀]-distributivityₗ) {x}{y}{z} = p{x}{y}{z} where
    p : ∀{x y z : ℕ} → (x ⋅ (y −₀ z)) ≡ (x ⋅ y) −₀ (x ⋅ z)
    p{x}{y}{z} =
      x ⋅ (y −₀ z)       🝖[ _≡_ ]-[ commutativity(_⋅_) {x}{y −₀ z} ]
      (y −₀ z) ⋅ x       🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(_−₀_) {y}{z}{x} ]
      (y ⋅ x) −₀ (z ⋅ x) 🝖[ _≡_ ]-[ congruence₂(_−₀_) (commutativity(_⋅_) {y}{x}) (commutativity(_⋅_) {z}{x}) ]
      (x ⋅ y) −₀ (x ⋅ z) 🝖-end

[⋅]-cancellationₗ : ∀{x} → ⦃ pos : Positive(x) ⦄ → (Names.CancellationOnₗ(_⋅_)(x))
[⋅]-cancellationₗ {𝐒 a}{b}{c} p with [<]-trichotomy {b}{c}
... | [∨]-introₗ ([∨]-introₗ lt) with () ← [<]-to-[≢] ([<]-with-[⋅]ₗ {a = a} lt) p
... | [∨]-introₗ ([∨]-introᵣ eq) = eq
... | [∨]-introᵣ gt              with () ← [>]-to-[≢] ([<]-with-[⋅]ₗ {a = a} gt) p

[⋅]-cancellationᵣ : ∀{x} → ⦃ pos : Positive(x) ⦄ → (Names.CancellationOnᵣ(_⋅_)(x))
[⋅]-cancellationᵣ {𝐒 c}{a}{b} p with [<]-trichotomy {a}{b}
... | [∨]-introₗ ([∨]-introₗ lt) with () ← [<]-to-[≢] ([<]-with-[⋅]ᵣ {c = c} lt) p
... | [∨]-introₗ ([∨]-introᵣ eq) = eq
... | [∨]-introᵣ gt              with () ← [>]-to-[≢] ([<]-with-[⋅]ᵣ {c = c} gt) p
