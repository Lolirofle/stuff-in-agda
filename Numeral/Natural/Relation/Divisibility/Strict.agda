module Numeral.Natural.Relation.Divisibility.Strict where

open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Relation.Divisibility
open import Relator.Equals
open import Type

_∣≢_ : ℕ → ℕ → Type
a ∣≢ b = (a ∣ b) ∧ (a ≢ b)

open import Functional
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Logic.Propositional.Theorems
open import Relator.Equals.Proofs.Equiv
import      Relator.Ordering.Proofs
open import Structure.Relator.Ordering
open import Structure.Relator.Properties

[∣≢]-def-[∣][≢] : ∀{a b} → (a ∣≢ b) ↔ ((a ∣ b) ∧ (a ≢ b))
[∣≢]-def-[∣][≢] = [↔]-reflexivity

instance
  [∣≢]-irreflexivity : Irreflexivity(_∣≢_)
  [∣≢]-irreflexivity = Relator.Ordering.Proofs.From-[≤][<].By-[≤].[<]-irreflexivity (_∣_)(_∣≢_) [∣≢]-def-[∣][≢]

instance
  [∣≢]-asymmetry : Asymmetry(_∣≢_)
  [∣≢]-asymmetry = Relator.Ordering.Proofs.From-[≤][<].By-[≤].By-antisymmetry.[<]-asymmetry (_∣_)(_∣≢_) [∣≢]-def-[∣][≢]

instance
  [∣≢]-transitivity : Transitivity(_∣≢_)
  [∣≢]-transitivity = Relator.Ordering.Proofs.From-[≤][<].By-[≤].[<]-transitivity-by-asym-trans (_∣_)(_∣≢_) [∣≢]-def-[∣][≢]

instance
  [∣≢]-strictPartialOrder : Strict.PartialOrder(_∣≢_)
  [∣≢]-strictPartialOrder = record{}

open import Data
open import Data.Boolean.Stmt
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Numeral.Natural.Relation.Proofs

instance
  [∣≢]-wellFounded : ∀{n} ⦃ pos : Positive(n) ⦄ → Strict.Properties.Accessibleₗ(_∣≢_)(n)
  [∣≢]-wellFounded {n} = ℕ-strong-recursion(\x → ⦃ pos : Positive(x) ⦄ → Strict.Properties.Accessibleₗ(_∣≢_)(x)) rec n where
    rec : (n : ℕ) → ((i : ℕ) → (i < n) → ⦃ pos : Positive(i) ⦄ → Strict.Properties.Accessibleₗ(_∣≢_)(i)) → ⦃ pos : Positive n ⦄ → Strict.Properties.Accessibleₗ(_∣≢_)(n)
    rec x prev ⦃ pos ⦄ = Strict.Properties.intro ⦃ \{ {.y} ⦃ [∧]-intro (Div𝐒{y}{z} div) ne ⦄ → Strict.Properties.intro ⦃ \{w} ⦃ wy ⦄ → Strict.Properties.Accessibleₗ.proof (prev y ([<]-of-[+]ₗ ⦃ Positive-not-[+] ne ⦄) ⦃ [∨]-elim id (divides-positive div) ([↔]-to-[←] [+]-positive pos) ⦄) {w} ⦃ wy ⦄ ⦄ } ⦄

private variable n a b : ℕ

[∣≢]-of-0ₗ : ¬(0 ∣≢ n)
[∣≢]-of-0ₗ ([∧]-intro div neq)
  with [≡]-intro ← [0]-only-divides-[0] div
  with () ← neq [≡]-intro

[∣≢]-of-1ₗ : ⦃ IsTrue(n ≢? 1) ⦄ → (1 ∣≢ n)
[∣≢]-of-1ₗ {𝟎}       = [∧]-intro Div𝟎 \()
[∣≢]-of-1ₗ {𝐒(𝐒(n))} = [∧]-intro [1]-divides \()

[∣≢]-of-1ᵣ : ¬(n ∣≢ 1)
[∣≢]-of-1ᵣ ([∧]-intro div neq) = neq([1]-only-divides-[1] div)

[∣≢]-of-[⋅]ₗ : ∀{a b} → ⦃ Positive(a) ⦄ → ⦃ IsTrue(b >? 1) ⦄ → (a ∣≢ a ⋅ b)
[∣≢]-of-[⋅]ₗ a@{𝐒 A} b@{𝐒(𝐒 _)} = [∧]-intro
  (divides-with-[⋅] {a}{a}{b} ([∨]-introₗ (reflexivity(_∣_))))
  ([<]-to-[≢] ([⋅]ₗ-strictly-growing{A}{b} (succ (succ min))))

[∣≢]-of-[⋅]ᵣ : ∀{a b} → ⦃ IsTrue(a >? 1) ⦄ → ⦃ Positive(b) ⦄ → (b ∣≢ a ⋅ b)
[∣≢]-of-[⋅]ᵣ a@{𝐒(𝐒 _)} b@{𝐒 B} = [∧]-intro
  (divides-with-[⋅] {𝐒 B}{a}{𝐒 B} ([∨]-introᵣ (reflexivity(_∣_))))
  ([<]-to-[≢] ([⋅]ᵣ-strictly-growing{B}{a} (succ (succ min))))
