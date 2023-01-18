module Numeral.Natural.Function.GreatestCommonDivisor.Relation.Proofs where

open import Functional
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Divisibility.Proofs.Modulo
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Function.GreatestCommonDivisor.Algorithm
open import Relator.Equals
open import Relator.Equals.Proofs
open import Sets.PredicateSet using (_∈_ ; _⊆_ ; _⊇_)
open import Structure.Relator
open import Structure.Relator.Properties
open import Structure.Setoid.Uniqueness

private variable a b c d d₁ d₂ n a₁ a₂ b₁ b₂ : ℕ

Gcd-unique : Unique(Gcd a b)
Gcd-unique p q = antisymmetry(_∣_)(_≡_)
  (Gcd.maximum₂ q (Gcd.divisorₗ p) (Gcd.divisorᵣ p))
  (Gcd.maximum₂ p (Gcd.divisorₗ q) (Gcd.divisorᵣ q))

Gcd-commutativity : Gcd(a)(b) ⊆ Gcd(b)(a)
Gcd-commutativity p = Gcd.intro₂
  (Gcd.divisorᵣ p)
  (Gcd.divisorₗ p)
  (swap(Gcd.maximum₂ p))

Gcd-identityᵣ : (a ∈ Gcd(a)(𝟎))
Gcd-identityᵣ = Gcd.intro₂
  (reflexivity(_∣_))
  Div𝟎
  const

Gcd-identityₗ : (a ∈ Gcd(𝟎)(a))
Gcd-identityₗ = Gcd-commutativity Gcd-identityᵣ

Gcd-onₗ-mod : ∀{a b} ⦃ pos : Positive(b) ⦄ → Gcd(a mod b)(b) ⊆ Gcd(a)(b)
Gcd-onₗ-mod {a}{𝐒 b} p = Gcd.intro₂
  ([↔]-to-[←] (divides-mod (Gcd.divisorᵣ p)) (Gcd.divisorₗ p))
  (Gcd.divisorᵣ p)
  (\da db → Gcd.maximum₂ p ([↔]-to-[→] (divides-mod db) da) db)

Gcd-onᵣ-mod : ∀{a b} ⦃ pos : Positive(a) ⦄ → Gcd(a)(b mod a) ⊆ Gcd(a)(b)
Gcd-onᵣ-mod = Gcd-commutativity ∘ Gcd-onₗ-mod ∘ Gcd-commutativity

Gcd-idempotence : a ∈ Gcd a a
Gcd-idempotence = Gcd.intro₂ (reflexivity(_∣_)) (reflexivity(_∣_)) (const id)

-- TODO: Lcm-lcm is in Numeral.Natural.Function.LeastCommonMultiple.Proofs while this is here. A bit inconsistent
Gcd-gcd : Gcd a b (gcd a b)
Gcd-gcd{a}{b} = gcdAlgorithmIntro ℕ (\{a}{b} g → Gcd a b g)
  (\ord → Gcd-onₗ-mod ∘ Gcd-commutativity)
  (const Gcd-identityᵣ)
  (const Gcd-commutativity)
  Gcd-idempotence
  a
  b

-- Usage: This allows the transferrence of proofs between `Gcd` and `gcd`. It is sometimes easier to prove properties by using `Gcd` first and then transfering them so that the proofs also hold for `gcd`.
-- TODO: This can be generalized to arbitrary function relations. For example, it also holds for lcm and Lcm
Gcd-gcd-value : (Gcd a b d) ↔ (gcd a b ≡ d)
Gcd-gcd-value = [↔]-intro (\{[≡]-intro → Gcd-gcd}) (Gcd-unique Gcd-gcd)

Gcd-sub-to-super : (Gcd a₁ b₁ ⊆ Gcd a₂ b₂) → (Gcd a₁ b₁ ⊇ Gcd a₂ b₂)
Gcd-sub-to-super f g = substitute₁ᵣ(Gcd _ _) (transitivity(_≡_) (Gcd-unique (f Gcd-gcd) Gcd-gcd) ([↔]-to-[→] Gcd-gcd-value g)) Gcd-gcd

Gcd-absorberₗ : 1 ∈ Gcd 1 a
Gcd-absorberₗ = Gcd.intro₂ [1]-divides [1]-divides const

Gcd-absorberᵣ : 1 ∈ Gcd a 1
Gcd-absorberᵣ = Gcd.intro₂ [1]-divides [1]-divides (const id)

Gcd-onₗ-[+]ᵣ-other : Gcd(a + b) b ⊆ Gcd a b
Gcd-onₗ-[+]ᵣ-other abbd =
  let dab = Gcd.divisorₗ abbd
      db  = Gcd.divisorᵣ abbd
      m   = Gcd.maximum₂ abbd
  in Gcd.intro₂ ([↔]-to-[←] (divides-without-[+] dab) db) db (\da db → m (divides-with-[+] da db) db)

Gcd-without-[⋅]ᵣ : ∀{a b c d} ⦃ pos : Positive(c)⦄ → Gcd(a ⋅ c)(b ⋅ c)(d ⋅ c) → Gcd a b d
Gcd-without-[⋅]ᵣ {a}{b}{𝐒 c} acbcdc =
  let dcac = Gcd.divisorₗ acbcdc
      dcbc = Gcd.divisorᵣ acbcdc
      m    = Gcd.maximum₂ acbcdc
  in Gcd.intro₂
    (divides-without-[⋅]ᵣ-both {z = c} dcac)
    (divides-without-[⋅]ᵣ-both {z = c} dcbc)
    (\{D} → Da ↦ Db ↦ divides-without-[⋅]ᵣ-both {z = c} (m{D ⋅ 𝐒(c)}
      (divides-with-[⋅]ᵣ-both {z = 𝐒(c)} Da)
      (divides-with-[⋅]ᵣ-both {z = 𝐒(c)} Db)
    ))

Gcd-of-successor : ∀{n} → (1 ∈ Gcd n (𝐒(n)))
Gcd-of-successor = Gcd.intro₂ [1]-divides [1]-divides p where
  p : ∀{d n} → (d ∣ n) → (d ∣ 𝐒(n)) → (d ∣ 1)
  p Div𝟎 dsn = dsn
  p (Div𝐒 dn) dsn = p dn ([↔]-to-[→] (divides-without-[+] dsn) (reflexivity(_∣_)))
