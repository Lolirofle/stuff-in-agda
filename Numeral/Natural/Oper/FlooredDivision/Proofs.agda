module Numeral.Natural.Oper.FlooredDivision.Proofs where

import      Lvl
open import Data
open import Data.Boolean.Stmt
open import Functional
open import Functional.Instance
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Numeral.Natural
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Comparisons.Proofs
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Algorithm
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Proofs
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Classical
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable d d₁ d₂ b a' b' : ℕ

[⌊/⌋][⌊/⌋₀]-equality : ∀{a b} → ⦃ _ : Positive(b)⦄ → (a ⌊/⌋₀ b ≡ a ⌊/⌋ b)
[⌊/⌋][⌊/⌋₀]-equality {b = 𝐒 b} = [≡]-intro

[⌊/⌋]-of-0ₗ : ∀{n} → ⦃ _ : IsTrue(positive?(n))⦄ → (𝟎 ⌊/⌋ n ≡ 𝟎)
[⌊/⌋]-of-0ₗ {𝐒 n} = [≡]-intro

[⌊/⌋]-of-1ₗ : ∀{n} → ⦃ _ : IsTrue(positive?(n))⦄ → ⦃ _ : IsTrue(n ≢? 1)⦄ → (1 ⌊/⌋ n ≡ 𝟎)
[⌊/⌋]-of-1ₗ {𝐒 (𝐒 n)} = [≡]-intro

[⌊/⌋]-of-1ᵣ : ∀{m} → (m ⌊/⌋ 1 ≡ m)
[⌊/⌋]-of-1ᵣ {𝟎} = [≡]-intro
[⌊/⌋]-of-1ᵣ {𝐒 m} = inddiv-result-𝐒 {0}{0}{m}{0} 🝖 congruence₁(𝐒) ([⌊/⌋]-of-1ᵣ {m})

[⌊/⌋]-of-same : ∀{n} ⦃ pos-n : Positive(n)⦄ → (n ⌊/⌋ n ≡ 1)
[⌊/⌋]-of-same {𝐒 n} = inddiv-of-denominator-successor {b' = n}

[⌊/⌋]-zero : ∀{a b} ⦃ pos-b : Positive(b)⦄ → (a < b) → (a ⌊/⌋ b ≡ 𝟎)
[⌊/⌋]-zero {a} {𝐒 b} (succ ord) = inddiv-lesser ord

[⌊/⌋]-step-[−₀] : ∀{a b} ⦃ pos-b : Positive(b)⦄ → (a ≥ b) → (a ⌊/⌋ b ≡ 𝐒((a −₀ b) ⌊/⌋ b))
[⌊/⌋]-step-[−₀] {𝐒 a} {𝐒 b} (succ ord) = inddiv-greater (succ ord) 🝖 inddiv-result-𝐒 {0}{b}{a −₀ b}{b}

[⌊/⌋]-step-[+] : ∀{a b} ⦃ pos-b : Positive(b)⦄ → ((a + b) ⌊/⌋ b ≡ 𝐒(a ⌊/⌋ b))
[⌊/⌋]-step-[+] {a}{b} = [⌊/⌋]-step-[−₀] ([≤]-of-[+]ᵣ {a}{b}) 🝖 congruence₁(𝐒) (congruence₁(_⌊/⌋ b) (inverseOperᵣ(_+_)(_−₀_) {a}{b}))

[⌊/⌋]-step₊-[−₀] : ∀{a b d} ⦃ pos-b : Positive(b)⦄ → (a ≥ b ⋅ d) → (a ⌊/⌋ b ≡ ((a −₀ (b ⋅ d)) ⌊/⌋ b) + d)
[⌊/⌋]-step₊-[−₀] {_}{_}{𝟎}   _   = reflexivity(_≡_)
[⌊/⌋]-step₊-[−₀] {a}{b}{𝐒 d} abd =
  a ⌊/⌋ b                              🝖[ _≡_ ]-[ congruence₁(_⌊/⌋ b) ([↔]-to-[→] ([−₀][+]-nullify2ᵣ {b}{a}) ([≤]-of-[+]ₗ 🝖 abd)) ]-sym
  ((a −₀ b) + b) ⌊/⌋ b                 🝖[ _≡_ ]-[ [⌊/⌋]-step-[+] {a −₀ b}{b} ]
  𝐒((a −₀ b) ⌊/⌋ b)                    🝖[ _≡_ ]-[ congruence₁(𝐒) ([⌊/⌋]-step₊-[−₀] {a −₀ b}{b}{d} (subtransitivityₗ(_≤_)(_≡_) (symmetry(_≡_) (inverseOperᵣ(swap(_+_))(_−₀_) {b ⋅ d}{b})) ([≤]-with-[−₀]ₗ {y = b} abd))) ]
  𝐒((((a −₀ b) −₀ (b ⋅ d)) ⌊/⌋ b) + d) 🝖[ _≡_ ]-[ congruence₁(_+ 𝐒(d)) {((a −₀ b) −₀ (b ⋅ d)) ⌊/⌋ b}{(a −₀ (b ⋅ 𝐒(d))) ⌊/⌋ b} (congruence₁(_⌊/⌋ b) ([−₀][−₀]-to-[−₀][+] {a}{b}{b ⋅ d})) ]
  ((a −₀ (b ⋅ 𝐒(d))) ⌊/⌋ b) + 𝐒(d) 🝖-end

[⌊/⌋]-positive : ∀{a b} ⦃ pos-b : Positive(b) ⦄ → (a ≥ b) ↔ Positive(a ⌊/⌋ b)
[⌊/⌋]-positive = [↔]-intro l r where
  l : ∀{a b} ⦃ pos-b : Positive(b) ⦄ → Positive(a ⌊/⌋ b) → (a ≥ b)
  l{𝐒 a}{𝐒 b} ab with [≤]-or-[>] {𝐒 b}{𝐒 a}
  ... | [∨]-introₗ p = p
  ... | [∨]-introᵣ p with () ← substitute₁ᵣ(Positive) ([⌊/⌋]-zero p) ab

  r : ∀{a b} ⦃ pos-b : Positive(b) ⦄ → (a ≥ b) → Positive(a ⌊/⌋ b)
  r ab rewrite [⌊/⌋]-step-[−₀] ab = <>

[⌊/⌋]-is-0 : ∀{a b} → ⦃ _ : Positive(b) ⦄ → (a ⌊/⌋ b ≡ 𝟎) → (a ≡ 𝟎) ∨ (a < b)
[⌊/⌋]-is-0 {𝟎}   {𝐒 b} _   = [∨]-introₗ [≡]-intro
[⌊/⌋]-is-0 {𝐒 a} {𝐒 b} zab with [≤]-or-[>] {𝐒 b}{𝐒 a}
... | [∨]-introₗ ord with () ← symmetry(_≡_) ([⌊/⌋]-step-[−₀] ord) 🝖 zab
... | [∨]-introᵣ ord = [∨]-introᵣ ord

[≤][⌊/⌋]ₗ-preserving : ∀{a₁ a₂ b} ⦃ pos-b : Positive(b) ⦄ → (a₁ ≤ a₂) → (a₁ ⌊/⌋ b ≤ a₂ ⌊/⌋ b)
[≤][⌊/⌋]ₗ-preserving {a₁}{a₂}{b} ord = ℕ-strong-recursion(a₁ ↦ ∀(a₂) → (a₁ ≤ a₂) → (a₁ ⌊/⌋ b ≤ a₂ ⌊/⌋ b)) p a₁ a₂ ord where
  p : (a₁ : ℕ) → ((i : ℕ) → (i < a₁) → ∀(a₂) → (i ≤ a₂) → (i ⌊/⌋ b ≤ a₂ ⌊/⌋ b)) → (∀(a₂) → (a₁ ≤ a₂) → (a₁ ⌊/⌋ b ≤ a₂ ⌊/⌋ b))
  p a₁ prev a₂ ord with [≤]-or-[>] {b}{a₁}
  ... | [∨]-introₗ ge =
    a₁ ⌊/⌋ b           🝖[ _≡_ ]-[ [⌊/⌋]-step-[−₀] ge ]-sub
    𝐒((a₁ −₀ b) ⌊/⌋ b) 🝖[ _≤_ ]-[ succ (prev(a₁ −₀ b) ([−₀]-strictly-lesser ge) (a₂ −₀ b) ([≤][−₀]ₗ-preserving {b = b} ord)) ]
    𝐒((a₂ −₀ b) ⌊/⌋ b) 🝖[ _≡_ ]-[ symmetry(_≡_) ([⌊/⌋]-step-[−₀] (ge 🝖 ord)) ]-sub
    a₂ ⌊/⌋ b           🝖-end
  ... | [∨]-introᵣ lt =
    a₁ ⌊/⌋ b 🝖[ _≡_ ]-[ [⌊/⌋]-zero lt ]-sub
    𝟎        🝖[ _≤_ ]-[ min ]
    a₂ ⌊/⌋ b 🝖-end

open import Numeral.Natural.Relation.Divisibility.Proofs
[<][⌊/⌋]ₗ-preserving : ∀{a₁ a₂ b} ⦃ pos-b : Positive(b) ⦄ → (b ∣ a₂) → (a₁ < a₂) → (a₁ ⌊/⌋ b < a₂ ⌊/⌋ b)
[<][⌊/⌋]ₗ-preserving {a₁} {a₂} {b} div ord = ℕ-strong-recursion(a₁ ↦ ∀(a₂) → (b ∣ a₂) → (a₁ < a₂) → (a₁ ⌊/⌋ b < a₂ ⌊/⌋ b)) p a₁ a₂ div ord where
  p : (a₁ : ℕ) → ((i : ℕ) → (i < a₁) → ∀(a₂) → (b ∣ a₂) → (i < a₂) → (i ⌊/⌋ b < a₂ ⌊/⌋ b)) → (∀(a₂) → (b ∣ a₂) → (a₁ < a₂) → (a₁ ⌊/⌋ b < a₂ ⌊/⌋ b))
  p a₁ prev a₂ div ord with [≤]-or-[>] {b}{a₁}
  ... | [∨]-introₗ ge =
    a₁ ⌊/⌋ b           🝖[ _≡_ ]-[ [⌊/⌋]-step-[−₀] ge ]-sub
    𝐒((a₁ −₀ b) ⌊/⌋ b) 🝖[ _<_ ]-[ succ (prev(a₁ −₀ b) ([−₀]-strictly-lesser ge) (a₂ −₀ b) (Div𝐏-monus div) (subtransitivityₗ(_≤_)(_≡_) (symmetry(_≡_) ([↔]-to-[→] [−₀][𝐒]ₗ-equality ge)) ([≤][−₀]ₗ-preserving {b = b} ord))) ]-super
    𝐒((a₂ −₀ b) ⌊/⌋ b) 🝖[ _≡_ ]-[ [⌊/⌋]-step-[−₀] {a₂}{b} (subtransitivityᵣ(_≤_)(_<_) ge ord) ]-sym
    a₂ ⌊/⌋ b           🝖-end
  ... | [∨]-introᵣ lt =
    a₁ ⌊/⌋ b 🝖[ _≡_ ]-[ [⌊/⌋]-zero lt ]-sub
    𝟎        🝖[ _<_ ]-[ [↔]-to-[→] Positive-greater-than-zero ([↔]-to-[→] [⌊/⌋]-positive (divides-upper-limit ⦃ Positive-greater-than ord ⦄ div)) ]-super
    a₂ ⌊/⌋ b 🝖[ _≡_ ]-end

open import Numeral.Natural.Relation.Order.Existence using ([≤]-equivalence ; [≤]-witness-order)
open import Logic.Predicate
[⌊/⌋]-elim : ∀{ℓ}{P : {ℕ} → ℕ → Type{ℓ}}{b} ⦃ pos-b : Positive(b) ⦄ → (∀{a} → (a < b) → P{a}(𝟎)) → (∀{a} → P{a}(a ⌊/⌋ b) → P{a + b}(𝐒(a ⌊/⌋ b))) → ∀{a} → P{a}(a ⌊/⌋ b)
[⌊/⌋]-elim {P = P}{b@(𝐒 B)} base step {a} = ℕ-strong-recursion(a ↦ P{a}(a ⌊/⌋ b))
  (a ↦ prev ↦ [∨]-elim
    (ba ↦
      let [∃]-intro x ⦃ xeq ⦄ = [↔]-to-[←] [≤]-equivalence ba
      in substitute₁ᵣ(a ↦ P{a}(a ⌊/⌋ b)) (commutativity(_+_) {x}{b} 🝖 xeq) (substitute₁ₗ(div ↦ P{x + b}(div)) ([⌊/⌋]-step-[+] {x}{b}) (step{x} (prev x ([↔]-to-[→] ([≤]-equivalence {𝐒(x)}) ([≤]-witness-order {B} ([∃]-intro (𝐒(x)) ⦃ xeq ⦄))))))
    )
    ((substitute₁ₗ(P) ∘ [⌊/⌋]-zero) ∘ₛ base)
    ([≤]-or-[>] {b}{a})
  ) a

-- [⌊/⌋]-elim2 : ∀{ℓ}{P : {ℕ} → ℕ → Type{ℓ}}{b} ⦃ pos-b : Positive(b) ⦄ → (∀{a} → (a < b) → P{a}(𝟎)) → ∀{m₂} → (m₂ < b) → (∀{a m₁} → (b ∣ a) → (m₁ < b) → P{a + m₁}((a + m₁) ⌊/⌋ b) → P{b + a + m₂}((b + a + m₂) ⌊/⌋ b)) → ∀{a} → P{a}(a ⌊/⌋ b)

-- [⌊/⌋]-elim2 : ∀{ℓ}{P : {ℕ} → ℕ → Type{ℓ}}{b} ⦃ pos-b : Positive(b) ⦄ → (∀{a₁ a₂} → (a₁ mod b ≡ a₂ mod b) → P{a₁}(a₁ ⌊/⌋ b) → P{a₂}(a₂ ⌊/⌋ b)) → ∀{a} → P{a}(a ⌊/⌋ b)

[≤][⌊/⌋]ᵣ-antipreserving : ∀{a b₁ b₂} ⦃ pos-b₂ : Positive(b₂) ⦄ → (ord : b₁ ≥ b₂) →
  let instance _ = [≤]-to-positive ord pos-b₂
  in (a ⌊/⌋ b₁ ≤ a ⌊/⌋ b₂)
[≤][⌊/⌋]ᵣ-antipreserving {a} {b₁} {b₂} ⦃ pos-b₂ ⦄ ord = ℕ-strong-recursion(a ↦ a ⌊/⌋ b₁ ≤ a ⌊/⌋ b₂) p a where
    instance
      pos-b₁ : Positive(b₁)
      pos-b₁ = [≤]-to-positive ord pos-b₂

    p : (a : ℕ) → ((i : ℕ) → (i < a) → (i ⌊/⌋ b₁ ≤ i ⌊/⌋ b₂)) → ((a ⌊/⌋ b₁) ≤ a ⌊/⌋ b₂)
    p a prev with [≤]-or-[>] {b₁}{a}
    ... | [∨]-introₗ ge =
        a ⌊/⌋ b₁            🝖[ _≡_ ]-[ [⌊/⌋]-step-[−₀] ge ]-sub
        𝐒((a −₀ b₁) ⌊/⌋ b₁) 🝖[ _≤_ ]-[ succ (prev(a −₀ b₁) ([−₀]-strictly-lesser ge)) ]
        𝐒((a −₀ b₁) ⌊/⌋ b₂) 🝖[ _≤_ ]-[ succ([≤][⌊/⌋]ₗ-preserving {b = b₂} ([≤][−₀]ᵣ-antipreserving {a}{b₁}{b₂} ord)) ]
        𝐒((a −₀ b₂) ⌊/⌋ b₂) 🝖[ _≡_ ]-[ symmetry(_≡_) ([⌊/⌋]-step-[−₀] (ord 🝖 ge)) ]-sub
        a ⌊/⌋ b₂            🝖-end
    ... | [∨]-introᵣ lt =
      a ⌊/⌋ b₁ 🝖[ _≡_ ]-[ [⌊/⌋]-zero lt ]-sub
      𝟎        🝖[ _≤_ ]-[ min ]
      a ⌊/⌋ b₂ 🝖-end

[≤][⌊/⌋]-preserving : ∀{a₁ a₂ b₁ b₂} ⦃ pos-b₂ : Positive(b₂) ⦄ → (a₁ ≤ a₂) → (ord : b₁ ≥ b₂) →
  let instance _ = [≤]-to-positive ord pos-b₂
  in (a₁ ⌊/⌋ b₁ ≤ a₂ ⌊/⌋ b₂)
[≤][⌊/⌋]-preserving {a₁}{a₂}{b₁}{b₂} pa pb =
  (a₁ ⌊/⌋ b₁) ⦃ _ ⦄ 🝖[ _≤_ ]-[ [≤][⌊/⌋]ᵣ-antipreserving {a₁}{b₁}{b₂} pb ]
  a₁ ⌊/⌋ b₂         🝖[ _≤_ ]-[ [≤][⌊/⌋]ₗ-preserving {a₁}{a₂}{b₂} pa ]
  a₂ ⌊/⌋ b₂         🝖-end

-- TODO: Not true. For example a₁=0, a₂=1, b=2 (because (_ ⌊/⌋_) is non-injective). Can be resolved by comparing some mod b
-- postulate [<][⌊/⌋]ₗ-preserving : ∀{a₁ a₂ b} ⦃ pos-b : Positive(b) ⦄ → (a₁ < a₂) → (a₁ ⌊/⌋ b < a₂ ⌊/⌋ b)
{-[<][⌊/⌋]ₗ-preserving {a₁}{a₂}{b} ord = [≤][≢]-to-[<]
  ([≤][⌊/⌋]ₗ-preserving {b = b} (sub₂(_<_)(_≤_) ord))
  {!!}-}

[⌊/⌋]-leₗ : ∀{a b} ⦃ pos-b : Positive(b)⦄ → (a ⌊/⌋ b ≤ a)
[⌊/⌋]-leₗ {a}{b} = subtransitivityᵣ(_≤_)(_≡_) ([≤][⌊/⌋]ᵣ-antipreserving {a}{b}{1} ([↔]-to-[→] Positive-greater-than-zero infer)) [⌊/⌋]-of-1ᵣ
{- Very similar to the proof of [≤][⌊/⌋]ᵣ-antipreserving
ℕ-strong-recursion(a ↦ a ⌊/⌋ 𝐒(b) ≤ a) p a where
  p : (a : ℕ) → ((i : ℕ) → (i < a) → (i ⌊/⌋ 𝐒(b) ≤ i)) → ((a ⌊/⌋ 𝐒(b)) ≤ a)
  p a prev with [≤]-or-[>] {𝐒 b}{a}
  ... | [∨]-introₗ ge =
    let p2 =
          𝐒(a −₀ 𝐒(b))            🝖[ _≡_ ]-[ symmetry(_≡_) ([↔]-to-[→] [−₀][𝐒]ₗ-equality ge) ]-sub
          𝐒(a) −₀ 𝐒(b)            🝖[ _≤_ ]-[]
          a −₀ b                  🝖[ _≤_ ]-[ [−₀]-lesser {a}{b} ]
          a                       🝖-end
    in
      a ⌊/⌋ 𝐒(b)              🝖[ _≡_ ]-[ [⌊/⌋]-step-[−₀] ge ]-sub
      𝐒((a −₀ 𝐒(b)) ⌊/⌋ 𝐒(b)) 🝖[ _≤_ ]-[ succ(prev(a −₀ 𝐒 b) p2) ]
      𝐒(a −₀ 𝐒(b))            🝖[ _≤_ ]-[ p2 ]
      a                       🝖-end
  ... | [∨]-introᵣ lt =
    a ⌊/⌋ 𝐒(b) 🝖[ _≡_ ]-[ [⌊/⌋]-zero lt ]-sub
    𝟎          🝖[ _≤_ ]-[ min ]
    a          🝖-end
-}

[⌊/⌋]-ltₗ : ∀{a} ⦃ pos-a : Positive(a)⦄ {b} ⦃ b-proof : IsTrue(b >? 1)⦄ → ((a ⌊/⌋ b) ⦃ [<?]-positive-any {1}{b} ⦄ < a)
[⌊/⌋]-ltₗ {a@(𝐒 A)} {b@(𝐒(𝐒 B))} = [⌊/⌋]-elim{P = \{a} div → ⦃ Positive(a) ⦄ → (div < a)}
  (\{ {𝐒 A} _ → succ min })
  (\{
    {𝟎} _ → succ(succ min) ;
    {𝐒 a} prev → succ (prev 🝖 succ([≤]-of-[+]ₗ{a}{𝐒 B}))
  })

-- postulate [⌊/⌋]-associate-commute : ∀{a b c} ⦃ pos-b : Positive(b) ⦄ ⦃ pos-c : Positive(c) ⦄ → ((a ⌊/⌋ b) ⌊/⌋ c ≡ (a ⌊/⌋ c) ⌊/⌋ b)

[⌊/⌋]-operator : ∀{a₁ a₂ b₁ b₂} ⦃ pos-b₁ : Positive(b₁) ⦄ → (a₁ ≡ a₂) → (pb : b₁ ≡ b₂) → (a₁ ⌊/⌋ b₁ ≡ (a₂ ⌊/⌋ b₂) ⦃ substitute₁ᵣ(Positive) pb pos-b₁ ⦄)
[⌊/⌋]-operator [≡]-intro [≡]-intro = [≡]-intro

open import Structure.Function.Domain
[⌊/⌋]-one : ∀{a b} ⦃ pos-b : Positive(b) ⦄ → (b ≤ a < (b ⋅ 2)) ↔ (a ⌊/⌋ b ≡ 1)
[⌊/⌋]-one {a}{b} ⦃ pos-b ⦄ = [↔]-intro
  ([⌊/⌋]-elim
    {P = \{a} div → (b ≤ a < (b ⋅ 2)) ← (div ≡ 1)}{b = b}
    (\_ ())
    (\{a} p 𝐒div1 → [∧]-intro
      ([≤][+]ᵣ-same {𝟎}{a}{𝟎}{b} min)
      ([∨]-elim
        (\{[≡]-intro → [<][+]ᵣ-same {0}{b}{𝟎}{b} ([↔]-to-[→] Positive-greater-than-zero pos-b)})
        ([<][+]ᵣ-same {a}{b}{𝟎}{b})
        ([⌊/⌋]-is-0 {a}{b} (injective(𝐒) 𝐒div1))
      )
    )
    {a}
  )
  ([⌊/⌋]-elim
    {P = \{a} div → (b ≤ a < (b ⋅ 2)) → (div ≡ 1)}{b = b}
    (\ab ([∧]-intro ba _) → [⊥]-elim ([≤][𝐒]ₗ (ab 🝖 ba)))
    (\{a} _ ([∧]-intro _ abbb) → congruence₁(𝐒) ([⌊/⌋]-zero {a}{b} ([<][+]ᵣ-same {a}{b}{b}{0} abbb)))
    {a}
  )

{- TODO: Maybe this is unnecessary.
open import Lang.Inspect
[⌊/⌋]-greater-than-1 : ∀{a b} ⦃ pos-b : Positive(b) ⦄ → (a ≥ (b ⋅ 2)) ↔ (a ⌊/⌋ b > 1)
[⌊/⌋]-greater-than-1 {a}{b@(𝐒 B)} = [↔]-intro l r where
  l : ∀{a} → (a ≥ (b ⋅ 2)) ← (a ⌊/⌋ b > 1)
  l{a@(𝐒 _)} p = succ {![⌊/⌋]-positive!}

  r : ∀{a} → (a ≥ (b ⋅ 2)) → (a ⌊/⌋ b > 1)
  r{a@(𝐒 A)} ab with (a ⌊/⌋ b) | inspect (_⌊/⌋ b) a
  ... | 𝟎       | intro eq = {!!} -- with () ← substitute₁ᵣ(Positive) eq ([↔]-to-[→] [⌊/⌋]-positive ([≤]-predecessor ab))
  ... | 𝐒 𝟎     | intro eq = {![↔]-to-[←] ([⌊/⌋]-one {a}{b}) eq!}
  ... | 𝐒 (𝐒 d) | intro eq = succ(succ min)
  -- = {![↔]-to-[→] [⌊/⌋]-positive ([≤]-predecessor ab)!}

-- TODO: This is not necessarily true
[⌊/⌋]-greater-than-1 : ∀{a b} ⦃ pos-b : Positive(b) ⦄ → (b ∣ a) → (a > b) ↔ (a ⌊/⌋ b > 1)
[⌊/⌋]-greater-than-1 {𝟎}{b} ba = [↔]-intro (\p → [⊥]-elim ([≤][0]ᵣ-negation (subtransitivityᵣ(_<_)(_≡_) p ([⌊/⌋]-of-0ₗ {b})))) \()
[⌊/⌋]-greater-than-1 {a@(𝐒 A)}{b} ba = [↔]-intro l r where
  l : (a > b) ← (a ⌊/⌋ b > 1)
  l p = [≤][≢]-to-[<] (divides-upper-limit ba) \{[≡]-intro → [<]-to-[≢] p (symmetry(_≡_) ([⌊/⌋]-of-same {b}))}

  r : (a > b) → (a ⌊/⌋ b > 1)
  r p = subtransitivityᵣ(_<_)(_≡_) (succ ([↔]-to-[→] Positive-greater-than-zero ([↔]-to-[→] ([⌊/⌋]-positive {a −₀ b}{b}) {!!}))) (symmetry(_≡_) ([⌊/⌋]-step-[−₀] (sub₂(_<_)(_≤_) p)))

-}
