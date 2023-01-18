module Numeral.Natural.Function.GreatestCommonDivisor.Proofs where

open import Data
open import Functional
open import Logic.Propositional
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Function.GreatestCommonDivisor.Relation.Proofs
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator.Properties
open import Structure.Operator
open import Structure.Operator.Properties
open import Syntax.Transitivity

private variable a b c d d₁ d₂ n a₁ a₂ b₁ b₂ : ℕ

gcd-idempotence : (gcd(a)(a) ≡ a)
gcd-idempotence = [↔]-to-[→] Gcd-gcd-value Gcd-idempotence

instance
  gcd-identityₗ : Identityₗ(gcd)(𝟎)
  Identityₗ.proof gcd-identityₗ = [↔]-to-[→] Gcd-gcd-value Gcd-identityₗ

instance
  gcd-identityᵣ : Identityᵣ(gcd)(𝟎)
  Identityᵣ.proof gcd-identityᵣ = [↔]-to-[→] Gcd-gcd-value Gcd-identityᵣ

instance
  gcd-absorberₗ : Absorberₗ(gcd)(1)
  Absorberₗ.proof gcd-absorberₗ{b} = [↔]-to-[→] (Gcd-gcd-value{_}{b}) Gcd-absorberₗ

instance
  gcd-absorberᵣ : Absorberᵣ(gcd)(1)
  Absorberᵣ.proof gcd-absorberᵣ{a} = [↔]-to-[→] (Gcd-gcd-value{a}{_}) Gcd-absorberᵣ

instance
  gcd-commutativity : Commutativity(gcd)
  Commutativity.proof gcd-commutativity {x}{y} = [↔]-to-[→] (Gcd-gcd-value {x}{y}) (Gcd-commutativity Gcd-gcd)

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

gcd-of-mod : ∀{a b} ⦃ pos : Positive(b) ⦄ → (gcd(a mod b) b ≡ gcd a b)
gcd-of-mod{a}{b} = symmetry(_≡_) ([↔]-to-[→] (Gcd-gcd-value{a}{b}) (Gcd-onₗ-mod Gcd-gcd))

-- TODO: Is it neccessary to prove this? By gcd-dividesₗ and gcd-dividesᵣ, one get (gcd(a)(b) ∣ min(a)(b)) and the divisor is always smaller
-- gcd-min-order : (gcd(a)(b) ≤ min(a)(b))

gcd-with-[+] : (gcd(a + b)(b) ≡ gcd(a)(b))
gcd-with-[+] {a}{b} = symmetry(_≡_) ([↔]-to-[→] (Gcd-gcd-value{a}{b}) (Gcd-onₗ-[+]ᵣ-other Gcd-gcd))

gcd-with₁-[⋅]ₗ : (gcd(a ⋅ b)(b) ≡ b)
gcd-with₁-[⋅]ₗ {a}{b} = [↔]-to-[→] (Gcd-gcd-value {a ⋅ b}{b}) (Gcd.intro₂ (divides-with-[⋅] {b}{a} ([∨]-introᵣ (reflexivity(_∣_)))) (reflexivity(_∣_)) (const id))

open import Numeral.Natural.Oper.Proofs
gcd-with₁-[⋅]ᵣ : (gcd(a ⋅ b)(a) ≡ a)
gcd-with₁-[⋅]ᵣ {a}{b} = congruence₂-₁(gcd)(a) (commutativity(_⋅_) {a}{b}) 🝖 gcd-with₁-[⋅]ₗ {b}{a}

gcd-with₂-[⋅]ₗ : (gcd(b)(a ⋅ b) ≡ b)
gcd-with₂-[⋅]ₗ {b}{a} = commutativity(gcd) {b}{a ⋅ b} 🝖 gcd-with₁-[⋅]ₗ {a}{b}

gcd-with₂-[⋅]ᵣ : (gcd(a)(a ⋅ b) ≡ a)
gcd-with₂-[⋅]ᵣ {a}{b} = commutativity(gcd) {a}{a ⋅ b} 🝖 gcd-with₁-[⋅]ᵣ {a}{b}

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
open import Syntax.Implication

gcd-positive : (Positive(a) ∨ Positive(b)) ↔ Positive(gcd a b)
gcd-positive{a}{b} =
  Positive(a) ∨ Positive(b) ⇔-[ [∨]-map-[↔] Positive-non-zero Positive-non-zero ]
  (a ≢ 𝟎) ∨ (b ≢ 𝟎)         ⇔-[ [¬]-preserves-[∧][∨] ⦃ decider-classical(a ≡ 𝟎) ⦄ ⦃ decider-classical(b ≡ 𝟎) ⦄ ]-sym
  ¬((a ≡ 𝟎) ∧ (b ≡ 𝟎))      ⇔-[ [¬]-unaryOperator (gcd-0 {a}{b}) ]
  gcd a b ≢ 𝟎               ⇔-[ Positive-non-zero ]-sym
  Positive(gcd a b)         ⇔-end

{-

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
-}
