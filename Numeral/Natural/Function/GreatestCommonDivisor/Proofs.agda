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

private variable a b c d d₁ d₂ : ℕ

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

gcd-with-[⋅] : (gcd(a ⋅ c)(b ⋅ c) ≡ gcd(a)(b) ⋅ c)
gcd-with-[⋅] {a}{𝟎}   {b} = [≡]-intro
gcd-with-[⋅] {a}{𝐒(c)}{b} =
  gcd(a ⋅ 𝐒(c)) (b ⋅ 𝐒(c))                 🝖[ _≡_ ]-[ q ]-sym
  gcd(a ⋅ 𝐒(c)) (b ⋅ 𝐒(c)) ⌊/⌋ 𝐒(c) ⋅ 𝐒(c) 🝖[ _≡_ ]-[ congruence₂ₗ(_⋅_)(𝐒(c)) ([↔]-to-[→] Gcd-gcd-value (p{gcd(a ⋅ 𝐒(c))(b ⋅ 𝐒(c)) ⌊/⌋ 𝐒(c)} ([↔]-to-[←] Gcd-gcd-value (symmetry(_≡_) q)))) ]-sym
  gcd(a)(b) ⋅ 𝐒(c)                         🝖-end
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

[⌊/⌋₀]-gcd-coprime : (Positive(a) ∨ Positive(b)) → Coprime(a ⌊/⌋₀ gcd(a)(b)) (b ⌊/⌋₀ gcd(a)(b))
[⌊/⌋₀]-gcd-coprime {a}{b} nz =
  let d = gcd(a)(b)
      D = gcd(a ⌊/⌋₀ d) (b ⌊/⌋₀ d)
      gcd-D = Gcd-gcd {a ⌊/⌋₀ d} {b ⌊/⌋₀ d}
      d-pos = [↔]-to-[→] Positive-greater-than-zero ([↔]-to-[→] gcd-positive nz)
  in
    • (
      Gcd.divisorₗ gcd-D ⇒
      (D ∣ (a ⌊/⌋₀ d))         ⇒-[ divides-with-[⋅]ᵣ-both {z = d} ]
      (D ⋅ d ∣ (a ⌊/⌋₀ d) ⋅ d) ⇒-[ substitute₂ᵣ(_∣_) ([⋅][⌊/⌋₀]-inverseOperatorᵣ d-pos (gcd-dividesₗ {b = b})) ]
      (D ⋅ d ∣ a)              ⇒-[ substitute₂ₗ(_∣_) (commutativity(_⋅_) {D}{d}) ]
      (d ⋅ D ∣ a)              ⇒-end
    )
    • (
      Gcd.divisorᵣ gcd-D ⇒
      (D ∣ (b ⌊/⌋₀ d))         ⇒-[ divides-with-[⋅]ᵣ-both {z = d} ]
      (D ⋅ d ∣ (b ⌊/⌋₀ d) ⋅ d) ⇒-[ substitute₂ᵣ(_∣_) ([⋅][⌊/⌋₀]-inverseOperatorᵣ d-pos gcd-dividesᵣ) ]
      (D ⋅ d ∣ b)              ⇒-[ substitute₂ₗ(_∣_) (commutativity(_⋅_) {D}{d}) ]
      (d ⋅ D ∣ b)              ⇒-end
    )
    ⇒₂-[ Gcd.maximum₂ Gcd-gcd ]
    ((d ⋅ D) ∣ d)                ⇒-[]
    ((d ⋅ D) ∣ (d ⋅ 1))          ⇒-[ divides-without-[⋅]ₗ-both' d-pos ]
    (D ∣ 1)                      ⇒-[ [1]-only-divides-[1] ]
    (D ≡ 1)                      ⇒-[ [↔]-to-[←] Coprime-gcd ]
    Coprime(a ⌊/⌋₀ d) (b ⌊/⌋₀ d) ⇒-end

[⌊/⌋]-gcd-coprime : (nz : Positive(a) ∨ Positive(b)) → Coprime((a ⌊/⌋ gcd(a)(b)) ⦃ [↔]-to-[→] gcd-positive nz ⦄) ((b ⌊/⌋ gcd(a)(b)) ⦃ [↔]-to-[→] gcd-positive nz ⦄)
[⌊/⌋]-gcd-coprime {a}{b} nz = substitute₂(Coprime)
  ([⌊/⌋][⌊/⌋₀]-equality ⦃ [↔]-to-[→] gcd-positive nz ⦄)
  ([⌊/⌋][⌊/⌋₀]-equality ⦃ [↔]-to-[→] gcd-positive nz ⦄)
  ([⌊/⌋₀]-gcd-coprime nz)
