module Numeral.Natural.Function.GreatestCommonDivisor.Proofs where

open import Data
open import Functional
open import Logic.Propositional
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Divisibility.Proofs.Modulo
open import Numeral.Natural.Relation.Order
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator
open import Structure.Relator.Properties
open import Structure.Operator
open import Structure.Operator.Properties
open import Syntax.Number
open import Syntax.Transitivity

private variable a b c d d₁ d₂ n a₁ a₂ b₁ b₂ : ℕ

gcd-same : (gcd(a)(a) ≡ a)
gcd-same = [↔]-to-[→] Gcd-gcd-value (Gcd.intro₂ (reflexivity(_∣_)) (reflexivity(_∣_)) (const id))

instance
  gcd-identityₗ : Identityₗ(gcd)(𝟎)
  Identityₗ.proof gcd-identityₗ = [↔]-to-[→] Gcd-gcd-value (Gcd.intro₂ Div𝟎 (reflexivity(_∣_)) (const id))

instance
  gcd-identityᵣ : Identityᵣ(gcd)(𝟎)
  Identityᵣ.proof gcd-identityᵣ = [≡]-intro

instance
  gcd-absorberₗ : Absorberₗ(gcd)(1)
  Absorberₗ.proof gcd-absorberₗ{b} = [↔]-to-[→] (Gcd-gcd-value{_}{b}) (Gcd.intro₂ [1]-divides [1]-divides const)

instance
  gcd-absorberᵣ : Absorberᵣ(gcd)(1)
  Absorberᵣ.proof gcd-absorberᵣ{a} = [↔]-to-[→] (Gcd-gcd-value{a}{_}) (Gcd.intro₂ [1]-divides [1]-divides (const id))

instance
  gcd-commutativity : Commutativity(gcd)
  Commutativity.proof gcd-commutativity {x}{y} = [↔]-to-[→] (Gcd-gcd-value {x}{y}) (Gcd-swap Gcd-gcd)

instance
  gcd-associativity : Associativity(gcd)
  Associativity.proof gcd-associativity {x}{y}{z} = [↔]-to-[→] (Gcd-gcd-value) (assoc Gcd-gcd Gcd-gcd Gcd-gcd) where
    assoc : Gcd x y d₁ → Gcd y z d₂ → Gcd x d₂ d → Gcd d₁ z d
    assoc xyd₁ yzd₂ xd₂d =
      let d₁x   = Gcd.divisorₗ xyd₁
          d₁y   = Gcd.divisorᵣ xyd₁
          xyd₁m = Gcd.maximum₂ xyd₁
          d₂y   = Gcd.divisorₗ yzd₂
          d₂z   = Gcd.divisorᵣ yzd₂
          yzd₂m = Gcd.maximum₂ yzd₂
          dx    = Gcd.divisorₗ xd₂d
          dd₂   = Gcd.divisorᵣ xd₂d
          xd₂dm = Gcd.maximum₂ xd₂d
      in Gcd.intro₂
        (xyd₁m dx (dd₂ 🝖 d₂y))
        (dd₂ 🝖 d₂z)
        (\dd₁ dz → xd₂dm (dd₁ 🝖 d₁x) (xd₂dm (dd₁ 🝖 d₁x) (yzd₂m (dd₁ 🝖 d₁y) dz) 🝖 dd₂))

gcd-dividesₗ : (gcd(a)(b) ∣ a)
gcd-dividesₗ {a}{b} = Gcd.divisorₗ{a}{b} Gcd-gcd

gcd-dividesᵣ : (gcd(a)(b) ∣ b)
gcd-dividesᵣ {a}{b} = Gcd.divisorᵣ{a}{b} Gcd-gcd

gcd-divisors : (d ∣ a) → (d ∣ b) → (d ∣ gcd(a)(b))
gcd-divisors da db = Gcd.maximum₂ Gcd-gcd da db

gcd-of-mod : (gcd(a mod 𝐒(b))(𝐒(b)) ≡ gcd(a)(𝐒(b)))
gcd-of-mod{a}{b} = [↔]-to-[→] (Gcd-gcd-value{a mod 𝐒(b)}{𝐒(b)}) (p Gcd-gcd) where
  p : Gcd(a)(𝐒(b)) d → Gcd(a mod 𝐒(b))(𝐒(b)) d
  p abd =
    let da = Gcd.divisorₗ abd
        db = Gcd.divisorᵣ abd
        m  = Gcd.maximum₂ abd
    in Gcd.intro₂ ([↔]-to-[→] (divides-mod db) da) db (Dab ↦ Db ↦ m ([↔]-to-[←] (divides-mod Db) Dab) Db)

-- TODO: Is it neccessary to prove this? By gcd-dividesₗ and gcd-dividesᵣ, one get (gcd(a)(b) ∣ min(a)(b)) and the divisor is always smaller
-- gcd-min-order : (gcd(a)(b) ≤ min(a)(b))

gcd-with-[+] : (gcd(a + b)(b) ≡ gcd(a)(b))
gcd-with-[+] {a}{b} = [↔]-to-[→] Gcd-gcd-value (p Gcd-gcd) where
  p : Gcd(a)(b) d → Gcd(a + b)(b) d
  p abd =
    let da = Gcd.divisorₗ abd
        db = Gcd.divisorᵣ abd
        m  = Gcd.maximum₂ abd
    in Gcd.intro₂ (divides-with-[+] da db) db (Dab ↦ Db ↦ m ([↔]-to-[←] (divides-without-[+] Dab) Db) Db)

gcd-with₁-[⋅] : (gcd(a ⋅ b)(b) ≡ b)
gcd-with₁-[⋅] {a}{b} = [↔]-to-[→] (Gcd-gcd-value {a ⋅ b}{b}) (Gcd.intro₂ (divides-with-[⋅] {b}{a} ([∨]-introᵣ (reflexivity(_∣_)))) (reflexivity(_∣_)) (const id))

instance
  [⋅]-gcd-distributivityᵣ : Distributivityᵣ(_⋅_)(gcd)
  [⋅]-gcd-distributivityᵣ = intro(\{x}{y}{z} → proof{x}{y}{z}) where
    proof : (gcd(a)(b) ⋅ c ≡ gcd(a ⋅ c)(b ⋅ c))
    proof {a}{b}{𝟎}    = [≡]-intro
    proof {a}{b}{𝐒(c)} =
      gcd(a)(b) ⋅ 𝐒(c)                         🝖[ _≡_ ]-[ congruence₂-₁(_⋅_)(𝐒(c)) ([↔]-to-[→] Gcd-gcd-value (p{gcd(a ⋅ 𝐒(c))(b ⋅ 𝐒(c)) ⌊/⌋ 𝐒(c)} ([↔]-to-[←] Gcd-gcd-value (symmetry(_≡_) q)))) ]
      gcd(a ⋅ 𝐒(c)) (b ⋅ 𝐒(c)) ⌊/⌋ 𝐒(c) ⋅ 𝐒(c) 🝖[ _≡_ ]-[ q ]
      gcd(a ⋅ 𝐒(c)) (b ⋅ 𝐒(c))                 🝖-end
      where
        p : Gcd a b d ← Gcd(a ⋅ 𝐒(c))(b ⋅ 𝐒(c))(d ⋅ 𝐒(c))
        p acbcdc =
          let dcac = Gcd.divisorₗ acbcdc
              dcbc = Gcd.divisorᵣ acbcdc
              m    = Gcd.maximum₂ acbcdc
          in Gcd.intro₂ (divides-without-[⋅]ᵣ-both {z = c} dcac) (divides-without-[⋅]ᵣ-both {z = c} dcbc) (\{D} → Da ↦ Db ↦ divides-without-[⋅]ᵣ-both {z = c} (m{D ⋅ 𝐒(c)} (divides-with-[⋅]ᵣ-both {z = 𝐒(c)} Da) (divides-with-[⋅]ᵣ-both {z = 𝐒(c)} Db)))

        q = [⋅][⌊/⌋]-inverseOperatorᵣ (gcd-divisors{𝐒(c)}{a ⋅ 𝐒(c)}{b ⋅ 𝐒(c)} (divides-with-[⋅] {𝐒(c)}{a} ([∨]-introᵣ (reflexivity(_∣_)))) (divides-with-[⋅]  {𝐒(c)}{b} ([∨]-introᵣ (reflexivity(_∣_)))))

gcd-0 : ((a ≡ 𝟎) ∧ (b ≡ 𝟎)) ↔ (gcd a b ≡ 𝟎)
gcd-0 = [↔]-intro l r where
  l : ((a ≡ 𝟎) ∧ (b ≡ 𝟎)) ← (gcd a b ≡ 𝟎)
  l {𝟎}   {𝟎}   p = [∧]-intro [≡]-intro [≡]-intro
  l {𝐒 a} {𝐒 b} p
    with intro zv _ ← [↔]-to-[←] (Gcd-gcd-value{𝐒(a)}{𝐒(b)}) p
    with () ← [0]-divides-not (zv 𝟎)

  r : ((a ≡ 𝟎) ∧ (b ≡ 𝟎)) → (gcd a b ≡ 𝟎)
  r {𝟎} {𝟎} _ = [≡]-intro

open import Logic.Classical
open import Logic.Propositional.Theorems
open import Numeral.Natural.Decidable
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Proofs
open import Type.Properties.Decidable.Proofs

gcd-positive : (Positive(a) ∨ Positive(b)) ↔ Positive(gcd a b)
gcd-positive{a}{b} = [↔]-transitivity ([∨]-map-[↔] Positive-non-zero Positive-non-zero) ([↔]-transitivity ([↔]-symmetry ([¬]-preserves-[∧][∨] ⦃ decider-classical(a ≡ 𝟎) ⦄ ⦃ decider-classical(b ≡ 𝟎) ⦄)) ([↔]-transitivity ([¬]-unaryOperator (gcd-0 {a}{b})) ([↔]-symmetry Positive-non-zero)))

gcd-of-successor : ∀{n} → Gcd(n)(𝐒(n))(1)
gcd-of-successor = Gcd.intro₂ [1]-divides [1]-divides p where
  p : ∀{d n} → (d ∣ n) → (d ∣ 𝐒(n)) → (d ∣ 1)
  p Div𝟎 dsn = dsn
  p (Div𝐒 dn) dsn = p dn ([↔]-to-[→] (divides-without-[+] dsn) (reflexivity(_∣_)))

open import Logic.Propositional.Theorems
open import Numeral.Natural.Coprime
open import Numeral.Natural.Coprime.Proofs
open import Numeral.Natural.Oper.FlooredDivision.Proofs
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order.Proofs
open import Syntax.Implication

instance
  [⋅]-gcd-distributivityₗ : Distributivityₗ(_⋅_)(gcd)
  Distributivityₗ.proof [⋅]-gcd-distributivityₗ {x}{y}{z} =
    x ⋅ gcd y z        🝖[ _≡_ ]-[ commutativity(_⋅_) {x}{gcd y z} ]
    gcd y z ⋅ x        🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(gcd) {y}{z}{x} ]
    gcd(y ⋅ x)(z ⋅ x)  🝖[ _≡_ ]-[ congruence₂(gcd) (commutativity(_⋅_) {y}{x}) (commutativity(_⋅_) {z}{x}) ]
    gcd(x ⋅ y)(x ⋅ z)  🝖-end

-- Two numbers without their common divisors are coprime.
-- gcd returns the product of all the common divisors (the greatest). Dividing the numbers by this product will therefore remove all the common divisors by division being an inverse.
[⌊/⌋₀]-gcd-coprime : (Positive(a) ∨ Positive(b)) → Coprime(a ⌊/⌋₀ gcd(a)(b)) (b ⌊/⌋₀ gcd(a)(b))
[⌊/⌋₀]-gcd-coprime {a}{b} nz =
  let d = gcd(a)(b)
      D = gcd(a ⌊/⌋₀ d) (b ⌊/⌋₀ d)
      gcd-D = Gcd-gcd {a ⌊/⌋₀ d} {b ⌊/⌋₀ d}
      instance d-pos = [↔]-to-[→] gcd-positive nz
  in
    • (
      Gcd.divisorₗ gcd-D ⇒
      (D ∣ (a ⌊/⌋₀ d))         ⇒-[ divides-with-[⋅]ᵣ-both {z = d} ]
      (D ⋅ d ∣ (a ⌊/⌋₀ d) ⋅ d) ⇒-[ substitute₂ᵣ(_∣_) ([⋅][⌊/⌋₀]-inverseOperatorᵣ (gcd-dividesₗ {b = b})) ]
      (D ⋅ d ∣ a)              ⇒-[ substitute₂ₗ(_∣_) (commutativity(_⋅_) {D}{d}) ]
      (d ⋅ D ∣ a)              ⇒-end
    )
    • (
      Gcd.divisorᵣ gcd-D ⇒
      (D ∣ (b ⌊/⌋₀ d))         ⇒-[ divides-with-[⋅]ᵣ-both {z = d} ]
      (D ⋅ d ∣ (b ⌊/⌋₀ d) ⋅ d) ⇒-[ substitute₂ᵣ(_∣_) ([⋅][⌊/⌋₀]-inverseOperatorᵣ (gcd-dividesᵣ {a = a})) ]
      (D ⋅ d ∣ b)              ⇒-[ substitute₂ₗ(_∣_) (commutativity(_⋅_) {D}{d}) ]
      (d ⋅ D ∣ b)              ⇒-end
    )
    ⇒₂-[ Gcd.maximum₂ Gcd-gcd ]
    ((d ⋅ D) ∣ d)                ⇒-[]
    ((d ⋅ D) ∣ (d ⋅ 1))          ⇒-[ divides-without-[⋅]ₗ-both' ]
    (D ∣ 1)                      ⇒-[ [1]-only-divides-[1] ]
    (D ≡ 1)                      ⇒-[ [↔]-to-[←] Coprime-gcd ]
    Coprime(a ⌊/⌋₀ d) (b ⌊/⌋₀ d) ⇒-end

[⌊/⌋]-gcd-coprime : (nz : Positive(a) ∨ Positive(b)) → Coprime((a ⌊/⌋ gcd(a)(b)) ⦃ [↔]-to-[→] gcd-positive nz ⦄) ((b ⌊/⌋ gcd(a)(b)) ⦃ [↔]-to-[→] gcd-positive nz ⦄)
[⌊/⌋]-gcd-coprime {a}{b} nz = substitute₂(Coprime)
  ([⌊/⌋][⌊/⌋₀]-equality ⦃ [↔]-to-[→] gcd-positive nz ⦄)
  ([⌊/⌋][⌊/⌋₀]-equality ⦃ [↔]-to-[→] gcd-positive nz ⦄)
  ([⌊/⌋₀]-gcd-coprime nz)

import      Numeral.Natural.Function as ℕ

gcd-of-powers-min : (gcd(n ^ a)(n ^ b) ≡ n ^ ℕ.min(a)(b))
gcd-of-powers-min {n}{𝟎}  {𝟎}   = [≡]-intro
gcd-of-powers-min {n}{𝟎}  {𝐒 b} = absorberₗ(gcd)(1) {n ^ 𝐒(b)}
gcd-of-powers-min {n}{𝐒 a}{𝟎}   = absorberᵣ(gcd)(1) {n ^ 𝐒(a)}
gcd-of-powers-min {n}{𝐒 a}{𝐒 b} =
  gcd (n ^ 𝐒(a)) (n ^ 𝐒(b))       🝖[ _≡_ ]-[]
  gcd (n ⋅ (n ^ a)) (n ⋅ (n ^ b)) 🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(gcd) {n}{n ^ a}{n ^ b} ]-sym
  n ⋅ gcd (n ^ a) (n ^ b)         🝖[ _≡_ ]-[ congruence₂-₂(_⋅_)(n) (gcd-of-powers-min {n}{a}{b}) ]
  n ⋅ n ^ ℕ.min(a)(b)             🝖[ _≡_ ]-[]
  n ^ 𝐒(ℕ.min(a)(b))              🝖[ _≡_ ]-[]
  n ^ ℕ.min(𝐒(a))(𝐒(b))           🝖-end

open import Logic.Predicate
open import Numeral.Natural.Relation.Divisibility.Proofs.Product
open import Structure.Function
open import Structure.Operator.Proofs.Util

-- (a ⋅ b ≡ c) → (c ⌊/⌋ a)

postulate Lcm-lcm : Lcm a b (lcm a b)
-- Lcm-lcm = Lcm.intro₂ {!!} {!!} {!!}

[⋅]-gcd-lcm : gcd a b ⋅ lcm a b ≡ a ⋅ b
[⋅]-gcd-lcm {a}{b} = [⋅][⌊/⌋₀]-inverseOperatorₗ {a ⋅ b}{gcd a b} (divides-with-[⋅] {c = b} ([∨]-introₗ (Gcd.divisorₗ(Gcd-gcd{a}{b}))))

[⋅]-lcm-coprim : Coprime a b → (lcm a b ≡ a ⋅ b)
[⋅]-lcm-coprim {a}{b} coprim =
  lcm a b                🝖[ _≡_ ]-[ identityₗ(_⋅_)(𝟏) {lcm a b} ]-sym
  𝟏 ⋅ lcm a b            🝖[ _≡_ ]-[ congruence₂-₁(_⋅_)(lcm a b) ([↔]-to-[→] Coprime-gcd coprim) ]-sym
  gcd a b ⋅ lcm a b      🝖[ _≡_ ]-[ [⋅]-gcd-lcm {a}{b} ]
  a ⋅ b                  🝖-end

divides-[⋅]-lcm : lcm a b ∣ (a ⋅ b)
divides-[⋅]-lcm {a}{b} = Lcm.minimum₂(Lcm-lcm{a}{b}) (divides-with-[⋅] {c = b} ([∨]-introₗ (reflexivity(_∣_)))) (divides-with-[⋅] {b = a} ([∨]-introᵣ (reflexivity(_∣_))))

divides-with-[⋅]ₗ : Coprime a b → (a ∣ c) → (b ∣ c) → ((a ⋅ b) ∣ c)
divides-with-[⋅]ₗ {a}{b}{𝟎} _ _ _ = Div𝟎
divides-with-[⋅]ₗ {a}{b}{c@(𝐒 _)} coprim = substitute₂ₗ(_∣_) ([⋅]-lcm-coprim coprim) ∘₂ Lcm.minimum₂ (Lcm-lcm{a}{b}) {c}

coprime-divides-only-when-1 : Coprime a b → (a ∣ b) → (a ≡ 1)
coprime-divides-only-when-1 (intro cop) div = cop (reflexivity(_∣_)) div

{-
c = x ⋅ a
c = y ⋅ b

c ⋅ c = (x ⋅ a) ⋅ (y ⋅ b)
c ⋅ c = (x ⋅ y) ⋅ (a ⋅ b)
c     = ((x ⋅ y) ⋅ (a ⋅ b)) / c
c     = ((x ⋅ y) / c) ⋅ (a ⋅ b)



a ⋅ b = (c / (x ⋅ y)) ⋅ c
c ∣ (x ⋅ y)
-}

-- Coprime a b → (d ∣ (a ⋅ b)) → ((d ∣ a) ⊕ (d ∣ b) ⊕ (d ∣ (gcd d a) ⋅ (gcd d b)))

-- TODO: The purpose of this is to use it for gcd(a)(b) = gcd(p₁^na₁ ⋅ p₂^na₂)(p₁^nb₁ ⋅ p₂^nb₂) = p^min(na₁)(nb₁) ⋅ p^min(na₂)(nb₂)
postulate gcdₗ-multiplicative : Coprime a₁ a₂ → (gcd(a₁ ⋅ a₂)(b) ≡ (gcd a₁ b) ⋅ (gcd a₂ b))
{-gcdₗ-multiplicative {a₁}{a₂}{b} coprim = [↔]-to-[→] Gcd-gcd-value (p Gcd-gcd Gcd-gcd) where
  p : Gcd a₁ b d₁ → Gcd a₂ b d₂ → Gcd(a₁ ⋅ a₂)(b)(d₁ ⋅ d₂)
  p {d₁}{d₂} g1 g2 =
    let d₁a₁ = Gcd.divisorₗ g1
        d₁b  = Gcd.divisorᵣ g1
        ad₁m = Gcd.maximum₂ g1
        d₂a₂ = Gcd.divisorₗ g2
        d₂b  = Gcd.divisorᵣ g2
        bd₂m = Gcd.maximum₂ g2
    in Gcd.intro₂
      (divides-with-[⋅]-both d₁a₁ d₂a₂)
      (divides-with-[⋅]ₗ (divides-to-converse-coprime d₁a₁ d₂a₂ coprim) d₁b d₂b)
      (\{d} da₁a₂ db → divides-with-[⋅] ([∨]-elim2 (\p → ad₁m p db) (\p → bd₂m p db)
        let dlcm = substitute₂ᵣ(_∣_) (symmetry(_≡_) ([⋅]-lcm-coprim coprim)) da₁a₂
        in {!Lcm.minimum₂(Lcm-lcm{a₁}{a₂})!}
      ))
      -- [∨]-elim (\p → ad₁m p db) (\p → bd₂m p db)
      -- Gcd.maximum₂ (Gcd-gcd{d₁}{d₂}) {(d ⌊/⌋ lcm d₁ d₂) ⦃ ? ⦄}
      -- Lcm.minimum₂ (Lcm-lcm{d₁}{d₂}) {d}
-}

-- d ∣ lcm a₁ a₂

{-
d ∣ (a₁ ⋅ a₂)
d / (gcd d a₁) ∣ (a₁ / (gcd d a₁) ⋅ a₂)
d / (gcd d a₁) / (gcd d a₂) ∣ (a₁ / (gcd d a₁) ⋅ a₂ / (gcd d a₂))

d / (gcd d a₁) / (gcd d a₂) ∣ d₁
d / (gcd d a₁) / (gcd d a₂) ∣ d₂


(b ∣ c) → (a ∣ (b ⋅ c)) → (a ∣ c)
-}

{- TODO: Is this true?
gcd-[⋅]-cross-distribute : Coprime a₁ b₁ → Coprime a₂ b₂ → (gcd(a₁ ⋅ b₁)(a₂ ⋅ b₂) ≡ (gcd a₁ a₂) ⋅ (gcd b₁ b₂))
gcd-[⋅]-cross-distribute{a₁}{b₁}{a₂}{b₂} coprim1 coprim2 = [↔]-to-[→] Gcd-gcd-value (p Gcd-gcd Gcd-gcd) where
  p : Gcd a₁ a₂ d₁ → Gcd b₁ b₂ d₂ → Gcd(a₁ ⋅ b₁)(a₂ ⋅ b₂)(d₁ ⋅ d₂)
  p g1 g2 =
    let d₁a₁ = Gcd.divisorₗ g1
        d₁a₂ = Gcd.divisorᵣ g1
        ad₁m = Gcd.maximum₂ g1
        d₂b₁ = Gcd.divisorₗ g2
        d₂b₂ = Gcd.divisorᵣ g2
        bd₂m = Gcd.maximum₂ g2
    in Gcd.intro₂
      (divides-with-[⋅]-both d₁a₁ d₂b₁)
      (divides-with-[⋅]-both d₁a₂ d₂b₂)
      (\{d} da₁b₁ da₂b₂ → {!!})
      -- swap coprime-divides-of-[⋅] coprim1
      -- ad₁m{d} 
-}
