module Numeral.Natural.Relation.ModuloCongruence.Proofs where

open import Functional
open import Functional.Instance
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Function.Coprimalize.Proofs
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.ModuloCongruence
open import Numeral.Natural.Relation.ModuloCongruence.Equiv
open import Numeral.Natural.Relation.Order
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Proofs
open import Structure.Operator
open import Structure.Operator.Proofs.Util
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Implication
open import Syntax.Transitivity

private variable m n x y : ℕ

mod-congruence-loose-linear-map : ∀{f g₁ g₂ h : ℕ → ℕ} (add : ∀{a b} → (f(a + b) ≡ g₁(a) + g₂(b))) → (mul : ∀{a b} → (g₂(a ⋅ b) ≡ a ⋅ h(b))) → ∀{m} ⦃ pos : Positive(m) ⦄ → Function ⦃ mod-congruence-equiv m ⦄ ⦃ mod-congruence-equiv m ⦄ f
Function.congruence (mod-congruence-loose-linear-map {f}{g₁}{g₂}{h} add mul {𝐒 m}) {a}{b} = mod-intro₂(\{a}{b} am bm → (am ≡ bm) → (f(a) mod 𝐒(m) ≡ f(b) mod 𝐒(m))) {𝐒 m} (\{a}{b}{n₁}{n₂} → p{a}{b}{n₁}{n₂}) {a}{b} where
  p : ∀{a b n₁ n₂} → (a < 𝐒(m)) → (b < 𝐒(m)) → (a ≡ b) → (f(a + (n₁ ⋅ 𝐒(m))) mod 𝐒(m)) ≡ (f(b + (n₂ ⋅ 𝐒(m))) mod 𝐒(m))
  p {a}{b}{n₁}{n₂} am bm ab =
    f(a + (n₁ ⋅ 𝐒(m))) mod 𝐒(m)       🝖[ _≡_ ]-[ congruence₁(_mod 𝐒(m)) (add{a}{n₁ ⋅ 𝐒(m)}) ]
    (g₁(a) + g₂(n₁ ⋅ 𝐒(m))) mod 𝐒(m)  🝖[ _≡_ ]-[ congruence₁(_mod 𝐒(m)) (congruence₂-₂(_+_)(g₁(a)) (congruence₁(g₂) (commutativity(_⋅_) {n₁}{𝐒 m}))) ]
    (g₁(a) + g₂(𝐒(m) ⋅ n₁)) mod 𝐒(m)  🝖[ _≡_ ]-[ congruence₁(_mod 𝐒(m)) (congruence₂-₂(_+_)(g₁(a)) (mul{𝐒(m)}{n₁})) ]
    (g₁(a) + (𝐒(m) ⋅ h(n₁))) mod 𝐒(m) 🝖[ _≡_ ]-[ mod-of-modulus-sum-multiple{g₁(a)}{𝐒 m}{h(n₁)} ]
    g₁(a) mod 𝐒(m)                    🝖[ _≡_ ]-[ congruence₁(_mod 𝐒(m)) (congruence₁(g₁) ab) ]
    g₁(b) mod 𝐒(m)                    🝖[ _≡_ ]-[ mod-of-modulus-sum-multiple{g₁(b)}{𝐒 m}{h(n₂)} ]-sym
    (g₁(b) + (𝐒(m) ⋅ h(n₂))) mod 𝐒(m) 🝖[ _≡_ ]-[ congruence₁(_mod 𝐒(m)) (congruence₂-₂(_+_)(g₁(b)) (mul{𝐒(m)}{n₂})) ]-sym
    (g₁(b) + g₂(𝐒(m) ⋅ n₂)) mod 𝐒(m)  🝖[ _≡_ ]-[ congruence₁(_mod 𝐒(m)) (congruence₂-₂(_+_)(g₁(b)) (congruence₁(g₂) (commutativity(_⋅_) {n₂}{𝐒 m}))) ]-sym
    (g₁(b) + g₂(n₂ ⋅ 𝐒(m))) mod 𝐒(m)  🝖[ _≡_ ]-[ congruence₁(_mod 𝐒(m)) (add{b}{n₂ ⋅ 𝐒(m)}) ]-sym
    f(b + (n₂ ⋅ 𝐒(m))) mod 𝐒(m)       🝖-end


module _ {m} ⦃ pos : Positive(m) ⦄ where
  instance
    mod-congruence-𝐒-function : Function ⦃ mod-congruence-equiv m ⦄ ⦃ mod-congruence-equiv m ⦄ 𝐒
    mod-congruence-𝐒-function = mod-congruence-loose-linear-map {𝐒}{𝐒}{id}{id} (reflexivity(_≡_)) (reflexivity(_≡_)) {m}

  instance
    mod-congruence-[+]-operator : BinaryOperator ⦃ mod-congruence-equiv m ⦄ ⦃ mod-congruence-equiv m ⦄ ⦃ mod-congruence-equiv m ⦄ (_+_)
    mod-congruence-[+]-operator = binaryOperator-from-function ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ {_▫_ = _+_}
      ⦃ \{x} → functionₗ-from-commutative-functionᵣ ⦃ _ ⦄ ⦃ _ ⦄ {_+_} ⦃ r ⦄ ⦃ intro (\{x} → congruence₁(_mod m) (commutativity(_+_) {x})) ⦄ {x} ⦄
      ⦃ r ⦄
      where
        r : ∀{c} → Function ⦃ mod-congruence-equiv m ⦄ ⦃ mod-congruence-equiv m ⦄ (_+ c)
        r{c} = mod-congruence-loose-linear-map {_+ c}{_+ c}{id}{id} (\{a}{b} → One.commuteᵣ-assocₗ{_▫_ = _+_} {a}{b}{c}) (reflexivity(_≡_)) {m}
        -- r {_}{_}{𝟎}  {_} p = p
        -- r {a}{b}{𝐒 c}{m} p = mod-congruence-with-𝐒 {a + c}{b + c}{m} (r {a}{b}{c}{m} p)

  instance
    mod-congruence-[⋅]-operator : BinaryOperator ⦃ mod-congruence-equiv m ⦄ ⦃ mod-congruence-equiv m ⦄ ⦃ mod-congruence-equiv m ⦄ (_⋅_)
    mod-congruence-[⋅]-operator = binaryOperator-from-function ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ {_▫_ = _⋅_}
      ⦃ \{x} → functionₗ-from-commutative-functionᵣ ⦃ _ ⦄ ⦃ _ ⦄ {_⋅_} ⦃ \{c} → r{c} ⦄ ⦃ intro (\{x}{y} → congruence₁(_mod m) (commutativity(_⋅_) {x}{y})) ⦄ {x} ⦄
      ⦃ \{c} → r{c} ⦄
      where
        r : ∀{c} → Function ⦃ mod-congruence-equiv m ⦄ ⦃ mod-congruence-equiv m ⦄ (_⋅ c)
        r{c} = mod-congruence-loose-linear-map {_⋅ c}{_⋅ c}{_⋅ c}{_⋅ c} (\{a}{b} → distributivityᵣ(_⋅_)(_+_) {a}{b}{c}) (\{a}{b} → associativity(_⋅_) {a}{b}{c}) {m}

  mod-congruence-[^]ₗ-function : ∀{n} → Function ⦃ mod-congruence-equiv m ⦄ ⦃ mod-congruence-equiv m ⦄ (_^ n)
  Function.congruence (mod-congruence-[^]ₗ-function {𝟎})           _ = reflexivity(_≡_)
  Function.congruence (mod-congruence-[^]ₗ-function {𝐒 n}) {a} {b} p = BinaryOperator.congruence ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ mod-congruence-[⋅]-operator {a}{b}{a ^ n}{b ^ n} p (Function.congruence ⦃ _ ⦄ ⦃ _ ⦄ (mod-congruence-[^]ₗ-function {n}) p)

instance
  mod-congruence-𝐒-injective : ⦃ pos : Positive(m) ⦄ → Injective ⦃ mod-congruence-equiv m ⦄ ⦃ mod-congruence-equiv m ⦄ 𝐒
  Injective.proof (mod-congruence-𝐒-injective {𝐒 m}) {a}{b} =
    𝐒(a) mod 𝐒(m) ≡ 𝐒(b) mod 𝐒(m)             ⇒-[ swap (BinaryOperator.congruence ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ (mod-congruence-[+]-operator {𝐒 m}) {𝐒 a}{𝐒 b}{m}{m}) (reflexivity(_≡_)) ]
    (𝐒(a) + m) mod 𝐒(m) ≡ (𝐒(b) + m) mod 𝐒(m) ⇒-[]
    (a + 𝐒(m)) mod 𝐒(m) ≡ (b + 𝐒(m)) mod 𝐒(m) ⇒-[ (p ↦ symmetry(_≡_) (mod-of-modulus-addᵣ{a}{m}) 🝖 p 🝖 mod-of-modulus-addᵣ{b}{m}) ]
    a mod 𝐒(m) ≡ b mod 𝐒(m)                   ⇒-end

mod-congruence-[𝄩] : ∀{a b m} → ⦃ pos : Positive(m) ⦄ → (a ≡ b [mod m ]) ↔ (m ∣ (a 𝄩 b))
mod-congruence-[𝄩] {a} {b} {𝐒 m} = [↔]-intro (l{a}{b}) (r{a}{b}) where
  l : ∀{a b} → (a mod 𝐒(m) ≡ b mod 𝐒(m)) ← (𝐒(m) ∣ (a 𝄩 b))
  l {𝟎}   {𝟎}   div = [≡]-intro
  l {𝟎}   {𝐒 b} div = symmetry(_≡_) ([↔]-to-[←] mod-divisibility div)
  l {𝐒 a} {𝟎}   div = [↔]-to-[←] mod-divisibility div
  l {𝐒 a} {𝐒 b} div = congruence₁ ⦃ mod-congruence-equiv _ ⦄ ⦃ mod-congruence-equiv _ ⦄ (𝐒) {a}{b} (l{a}{b} div)

  r : ∀{a b} → (a mod 𝐒(m) ≡ b mod 𝐒(m)) → (𝐒(m) ∣ (a 𝄩 b))
  r {𝟎}   {𝟎}   eq = Div𝟎
  r {𝟎}   {𝐒 b} eq = [↔]-to-[→] mod-divisibility (symmetry(_≡_) eq)
  r {𝐒 a} {𝟎}   eq = [↔]-to-[→] mod-divisibility eq
  r {𝐒 a} {𝐒 b} eq = r{a}{b} (injective ⦃ mod-congruence-equiv _ ⦄ ⦃ mod-congruence-equiv _ ⦄ (𝐒) {a}{b} eq)

mod-congruence-modₗ-function : ∀{m₁ m₂} ⦃ pos₁ : Positive(m₁) ⦄ ⦃ pos₂ : Positive(m₂) ⦄ → (m₁ ∣ m₂) → Function ⦃ mod-congruence-equiv m₁ ⦄ ⦃ mod-congruence-equiv m₁ ⦄ (_mod m₂)
Function.congruence (mod-congruence-modₗ-function{m₁@(𝐒 M₁)}{m₂} pdiv) {x}{y} xy =
  (x mod m₂) mod m₁ 🝖[ _≡_ ]-[ mod-nested-divisible pdiv ]
  x mod m₁          🝖[ _≡_ ]-[ xy ]
  y mod m₁          🝖[ _≡_ ]-[ mod-nested-divisible pdiv ]-sym
  (y mod m₂) mod m₁ 🝖-end

open import Logic.Propositional.Equiv using ([↔]-equiv)
open import Logic.Propositional.Theorems
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Function.GreatestCommonDivisor.Proofs
open import Numeral.Natural.Function.GreatestCommonDivisor.Relation.Proofs
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Compatibility
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse
open import Numeral.Natural.Coprime
open import Numeral.Natural.Coprime.Proofs
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Divisibility.Proofs.FlooredDivision
open import Numeral.Natural.Relation.Divisibility.Proofs.Productᵣ
open import Structure.Relator

mod-congruence-scale-modulus : ∀{m} → ⦃ pos : Positive(m) ⦄ → ∀{a b c} → (c ⋅ a ≡ c ⋅ b [mod m ]) ↔ (a ≡ b [mod((m ⌊/⌋ gcd c m) ⦃ _ ⦄)]) ⦃ _ ⦄
mod-congruence-scale-modulus {m} ⦃ pos ⦄ {a}{b}{c} = [↔]-transitivity  ([↔]-transitivity mod-congruence-[𝄩] ([↔]-intro l r)) ([↔]-symmetry (mod-congruence-[𝄩] ⦃ [↔]-to-[→] ([⌊/⌋]-positive ⦃ pgcd ⦄) (divides-upper-limit (Gcd.divisorᵣ (Gcd-gcd {a = c}))) ⦄)) where
  instance
    pgcd : Positive(gcd c m)
    pgcd = [↔]-to-[→] (gcd-positive {a = c}) ([∨]-introᵣ pos)

  l : (m ∣ ((c ⋅ a) 𝄩 (c ⋅ b))) ← ((m ⌊/⌋ gcd c m) ⦃ _ ⦄ ∣ (a 𝄩 b))
  l =
    (m ⌊/⌋ gcd c m) ∣ (a 𝄩 b)                         ⇒-[ divides-with-[⋅]ᵣ-both {z = gcd c m} ]
    ((m ⌊/⌋ gcd c m) ⋅ gcd c m) ∣ ((a 𝄩 b) ⋅ gcd c m) ⇒-[ substitute₂-₁ᵣ(_∣_) _ ([⋅][⌊/⌋]-inverseOperatorᵣ (Gcd.divisorᵣ (Gcd-gcd {a = c}))) ]
    m ∣ ((a 𝄩 b) ⋅ gcd c m)                           ⇒-[ divides-with-[⋅] {c = (c ⌊/⌋ gcd c m) ⦃ _ ⦄} ∘ [∨]-introₗ ]
    m ∣ ((a 𝄩 b) ⋅ gcd c m) ⋅ (c ⌊/⌋ gcd c m)         ⇒-[ substitute₂-₂ᵣ(_∣_) _ (associativity(_⋅_) {a 𝄩 b}{gcd c m}{(c ⌊/⌋ gcd c m) ⦃ _ ⦄}) ]
    m ∣ (a 𝄩 b) ⋅ (gcd c m ⋅ (c ⌊/⌋ gcd c m))         ⇒-[ substitute₂-₂ᵣ(_∣_) _ (congruence₂-₂(_⋅_)(a 𝄩 b) (symmetry(_≡_) ([⌊/⌋][⋅]ᵣ-compatibility {gcd c m}{c}{gcd c m} (Gcd.divisorₗ{c}{m} Gcd-gcd)))) ]
    m ∣ (a 𝄩 b) ⋅ ((gcd c m ⋅ c) ⌊/⌋ gcd c m)         ⇒-[ substitute₂-₂ᵣ(_∣_) _ (congruence₂-₂(_⋅_)(a 𝄩 b) ([⌊/⌋][swap⋅]-inverseOperatorᵣ {gcd c m}{c})) ]
    m ∣ (a 𝄩 b) ⋅ c                                   ⇒-[ substitute₂-₂ᵣ(_∣_) _ (commutativity(_⋅_) {a 𝄩 b}{c}) ]
    m ∣ c ⋅ (a 𝄩 b)                                   ⇒-[ substitute₂-₂ᵣ(_∣_) _ (distributivityₗ(_⋅_)(_𝄩_) {c}{a}{b}) ]
    m ∣ ((c ⋅ a) 𝄩 (c ⋅ b))                           ⇒-end

  r : (m ∣ ((c ⋅ a) 𝄩 (c ⋅ b))) → ((m ⌊/⌋ gcd c m) ⦃ _ ⦄ ∣ (a 𝄩 b))
  r =
    (m ∣ (c ⋅ a 𝄩 c ⋅ b))                                        ⇒-[ substitute₂-₂ₗ(_∣_) _ (distributivityₗ(_⋅_)(_𝄩_) {c}{a}{b}) ]
    (m ∣ c ⋅ (a 𝄩 b))                                            ⇒-[ divides-with-[⌊/⌋] {m}{c ⋅ (a 𝄩 b)}{gcd c m} ⦃ [∨]-introₗ ([∨]-introₗ pos) ⦄ (Gcd.divisorᵣ (Gcd-gcd {a = c})) ]
    (m ⌊/⌋ gcd c m) ⦃ _ ⦄ ∣ ((c ⋅ (a 𝄩 b)) ⌊/⌋ gcd c m) ⦃ _ ⦄    ⇒-[ substitute₂-₂ᵣ(_∣_) _ ([⌊/⌋][⋅]ₗ-compatibility {c}{a 𝄩 b}{gcd c m} ⦃ pgcd ⦄ (Gcd.divisorₗ {c}{m} Gcd-gcd)) ]
    (m ⌊/⌋ gcd c m) ⦃ _ ⦄ ∣ ((c ⌊/⌋ gcd c m) ⦃ pgcd ⦄ ⋅ (a 𝄩 b)) ⇒-[ swap(coprime-divides-of-[⋅] {(m ⌊/⌋ gcd c m) ⦃ _ ⦄}{(c ⌊/⌋ gcd c m) ⦃ _ ⦄}{a 𝄩 b}) (symmetry(Coprime) ([⌊/⌋]-gcd-coprime{c}{m} ⦃ [∨]-introᵣ pos ⦄)) ]
    ((m ⌊/⌋ gcd c m) ⦃ _ ⦄ ∣ (a 𝄩 b))                            ⇒-end

mod-congruence-modulus-by-divisibility : ∀{m₁} ⦃ pos-m₁ : Positive(m₁) ⦄ {m₂} ⦃ pos-m₂ : Positive(m₂) ⦄ → (m₂ ∣ m₁) → ∀{a b} → (a ≡ b [mod m₁ ]) → (a ≡ b [mod m₂ ])
mod-congruence-modulus-by-divisibility {m₁}{m₂} pdiv {a}{b} pmod =
  a mod m₂          🝖[ _≡_ ]-[ mod-nested-divisible pdiv ]-sym
  (a mod m₁) mod m₂ 🝖[ _≡_ ]-[ congruence₁(_mod m₂) pmod ]
  (b mod m₁) mod m₂ 🝖[ _≡_ ]-[ mod-nested-divisible pdiv ]
  b mod m₂ 🝖-end

mod-congruence-modulus-by-equality : ∀{m₁} ⦃ pos : Positive(m₁) ⦄ {m₂} → (eq : m₁ ≡ m₂) → ∀{a b} → (a ≡ b [mod m₁ ]) ↔ (a ≡ b [mod m₂ ]) ⦃ substitute₁ᵣ(Positive) eq pos ⦄
mod-congruence-modulus-by-equality [≡]-intro = [↔]-reflexivity

mod-congruence-scale : ∀{m} ⦃ pos-m : Positive(m) ⦄ {c} ⦃ pos-c : Positive(c) ⦄ → ∀{a b} → (a ≡ b [mod m ]) ↔ (c ⋅ a ≡ c ⋅ b [mod(c ⋅ m)]) ⦃ [⋅]-positiveᵣ {c}{m} infer infer ⦄
mod-congruence-scale {m}{c}{a}{b} = [↔]-transitivity (mod-congruence-modulus-by-equality eq) ([↔]-symmetry (mod-congruence-scale-modulus{c ⋅ m} ⦃ [↔]-to-[→] ([⋅]-positive {c}{m}) ([∧]-intro infer infer) ⦄ {a}{b}{c})) where
  eq =
    m                                 🝖[ _≡_ ]-[ [⌊/⌋][swap⋅]-inverseOperatorᵣ {c}{m} ]-sym
    ((c ⋅ m) ⌊/⌋ c) ⦃ _ ⦄             🝖[ _≡_ ]-[ [⌊/⌋]-operator [≡]-intro (symmetry(_≡_) (gcd-with₂-[⋅]ᵣ {c}{m})) ]
    ((c ⋅ m) ⌊/⌋ gcd c (c ⋅ m)) ⦃ _ ⦄ 🝖-end

-- postulate mod-congruence-divide : ∀{m} ⦃ pos-m : Positive(m) ⦄ {c} ⦃ pos-c : Positive(c) ⦄ → (div : (c ∣ m)) → ∀{a b} → (c ∣ a) → (c ∣ b) → (a ≡ b [mod m ]) → (a ⌊/⌋ c ≡ b ⌊/⌋ c [mod(m ⌊/⌋ c)]) ⦃ [↔]-to-[→] [⌊/⌋]-positive (divides-upper-limit div) ⦄

-- postulate mod-congruence-to-gcd-equality : ∀{m} ⦃ pos-m : Positive(m) ⦄ → ∀{a b} → (a ≡ b [mod m ]) → (gcd a m ≡ gcd b m)

-- postulate mod-congruence-[−₀]-operator : ∀{m} ⦃ pos-m : Positive(m) ⦄ → ∀{a₁ a₂ b₁ b₂} → (a₁ ≥ b₁) → (a₂ ≥ b₂) → (a₁ ≡ a₂ [mod m ]) → (b₁ ≡ b₂ [mod m ]) → (a₁ −₀ b₁ ≡ a₂ −₀ b₂ [mod m ])

-- postulate mod-congruence-[⌊/⌋]-operator : ∀{m} ⦃ pos-m : Positive(m) ⦄ → ∀{a₁ a₂ b₁ b₂} ⦃ pos-b₁ : Positive(b₁) ⦄ ⦃ pos-b₂ : Positive(b₂) ⦄ → (a₁ ∣ b₁) → (a₂ ∣ b₂) → (a₁ ≡ a₂ [mod m ]) → (b₁ ≡ b₂ [mod m ]) → (a₁ ⌊/⌋ b₁ ≡ a₂ ⌊/⌋ b₂ [mod m ])
