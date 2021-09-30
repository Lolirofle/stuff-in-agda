module Numeral.Natural.Function.GreatestCommonDivisor where

import Lvl
open import Data
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional
open import Numeral.CoordinateVector as Vector using (Vector)
open import Numeral.Finite using (𝕟 ; 𝟎 ; 𝐒)
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Classical
open import Type

-- TODO: Prove that gcd is the infimum in a lattice of ℕ with divisibility as its ordering

{-# TERMINATING #-}
gcdFold : ∀{ℓ}{T : Type{ℓ}} → ((a : ℕ) → (b : ℕ) → (a ≥ b) → (b > 𝟎) → T → T → T) → ((a : ℕ) → (b : ℕ) → (a < b) → (b > 𝟎) → T → T → T) → T → ℕ → ℕ → (ℕ ⨯ T)
gcdFold f g x (a)(𝟎) = (a , x)
gcdFold f g x (a)(𝐒(b)) with [≥]-or-[<] {a}{𝐒(b)}
... | [∨]-introₗ ab = Tuple.mapRight (f a (𝐒(b)) ab (succ min) x) (gcdFold f g x (𝐒(b))(a mod 𝐒(b)))
... | [∨]-introᵣ ba = Tuple.mapRight (g a (𝐒(b)) ba (succ min) x) (gcdFold f g x (𝐒(b))(a))

-- An algorithm for computing the greatest common divisor for two numbers.
-- Also called: Euclid's algorithm.
-- Termination: See `Gcd-existence` for a functionally equal variant of this function that passes the termination checker. It is equal in the sense that the same algorithm is used to construct the existence and to compute the value of this function. This is even more evident when looking at `Gcd-gcd`.
-- Alternative implementation:
--   gcd(a)(𝟎) = a
--   gcd(a)(𝐒(b)) with [≥]-or-[<] {a}{𝐒(b)}
--   ... | [∨]-introₗ _ = gcd(𝐒(b))(a mod 𝐒(b))
--   ... | [∨]-introᵣ _ = gcd(𝐒(b))(a)
gcd : ℕ → ℕ → ℕ
gcd a b = Tuple.left(gcdFold(\_ _ _ _ _ _ → <>) (\_ _ _ _ _ _ → <>) (<>{Lvl.𝟎}) a b)

lcm : ℕ → ℕ → ℕ
lcm(a)(b) = (a ⋅ b) ⌊/⌋₀ gcd(a)(b)

-- `Gcd a b D` is the specialization for 2 elements and states that `D` is a divisor of both `a` and `b`, and the greatest one of them.
-- Example:
--   Divisor(24) = {1,2,3,4,  6,8,   12,      24}
--   Divisor(60) = {1,2,3,4,5,6  ,10,12,15,20,   30,60}
--   24 = 2³ ⋅ 3¹
--   60 = 2² ⋅ 3¹ ⋅ 5¹
--   Gcd 24 60 = {max(Divisor(24) ∩ Divisor(60))} = 2² ⋅ 3¹ = 12
--   Divisor of first : 24 / 12 = 2
--   Divisor of second: 60 / 12 = 5
record GreatestCommonDivisor(n : ℕ) (v : Vector(n)(ℕ)) (D : ℕ) : Type{Lvl.𝟎} where
  constructor intro
  field
    divisor : ∀(i) → (D ∣ v(i))
    maximum : ∀{d} → (∀(i) → (d ∣ v(i))) → (d ∣ D)

Gcd = GreatestCommonDivisor(2) ∘₂ Vector.pair
module Gcd {a b D} where
  intro₂ : _ → _ → (∀{d} → _ → _ → (d ∣ D)) → Gcd a b D
  intro₂ divisorₗ divisorᵣ maximum = intro{2}{Vector.pair a b}
    (\{𝟎 → divisorₗ ; (𝐒(𝟎)) → divisorᵣ})
    (\dv → maximum (dv 𝟎) (dv (𝐒 𝟎)))
  module _ (inst : Gcd a b D) where
    open GreatestCommonDivisor(inst) public
    divisorₗ = divisor 𝟎
    divisorᵣ = divisor(𝐒 𝟎)
    maximum₂ = \{d} a b → maximum{d} \{𝟎 → a ; (𝐒(𝟎)) → b}

-- `Lcm a b M` is the specialization for 2 elements and states that `M` is a multiple of both `a` and `b`, and the smallest one of them.
-- Example:
--   360  = 2³ ⋅ 3² ⋅ 5¹
--   8400 = 2⁴ ⋅ 3¹ ⋅ 5² ⋅ 7¹
--   Lcm 360 8400 = {min(Multiple(360) ∩ Multiple(8400))} = 2⁴ ⋅ 3² ⋅ 5² ⋅ 7¹ = 25200
--   Multiple of first : 360 ⋅ 2¹ ⋅ 5¹ ⋅ 7¹ = 360 ⋅ 70 = 25200
--   Multiple of second: 8400 ⋅ 3¹ = 25200
record LeastCommonMultiple(n : ℕ) (v : Vector(n)(ℕ)) (M : ℕ) : Type{Lvl.𝟎} where
  constructor intro
  field
    multiple : ∀(i) → (v(i) ∣ M)
    minimum  : ∀{m} → (∀(i) → (v(i) ∣ m)) → (M ∣ m)

Lcm = LeastCommonMultiple(2) ∘₂ Vector.pair
module Lcm {a b M} where
  intro₂ : _ → _ → (∀{m} → _ → _ → (M ∣ m)) → Lcm a b M
  intro₂ multipleₗ multipleᵣ minimum = intro{2}{Vector.pair a b}
    (\{𝟎 → multipleₗ ; (𝐒(𝟎)) → multipleᵣ})
    (\dv → minimum (dv 𝟎) (dv (𝐒 𝟎)))
  module _ (inst : Lcm a b M) where
    open LeastCommonMultiple(inst) public
    multipleₗ = multiple 𝟎
    multipleᵣ = multiple(𝐒 𝟎)
    minimum₂ = \{m} a b → minimum{m} \{𝟎 → a ; (𝐒(𝟎)) → b}

open import Logic.Predicate
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Divisibility.Proofs.Modulo
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Sets.PredicateSet using (_∈_ ; _⊆_)
open import Structure.Relator.Properties
open import Structure.Setoid.Uniqueness
open import Syntax.Function

private variable a b d : ℕ

Gcd-unique : Unique(Gcd a b)
Gcd-unique p q = antisymmetry(_∣_)(_≡_)
  (Gcd.maximum₂ q (Gcd.divisorₗ p) (Gcd.divisorᵣ p))
  (Gcd.maximum₂ p (Gcd.divisorₗ q) (Gcd.divisorᵣ q))

Gcd-base : (a ∈ Gcd(a)(𝟎))
Gcd-base = Gcd.intro₂
  (reflexivity(_∣_))
  Div𝟎
  const

Gcd-step : (a ≥ 𝐒(b)) → Gcd(a mod 𝐒(b))(𝐒(b)) ⊆ Gcd(a)(𝐒(b))
Gcd-step ab p = Gcd.intro₂
  ([↔]-to-[←] (divides-mod (Gcd.divisorᵣ p)) (Gcd.divisorₗ p))
  (Gcd.divisorᵣ p)
  (\da db → Gcd.maximum₂ p ([↔]-to-[→] (divides-mod db) da) db)

Gcd-swap : Gcd(a)(b) ⊆ Gcd(b)(a)
Gcd-swap p = Gcd.intro₂
  (Gcd.divisorᵣ p)
  (Gcd.divisorₗ p)
  (swap(Gcd.maximum₂ p))

-- Note: The construction for the existence is following the same steps as in the definition of the function `gcd`, but unlike `gcd` which does not pass the termination checker, this uses ℕ-strong-induction to pass it.
Gcd-existence : ∃(Gcd a b)
Gcd-existence{a}{b} = ℕ-strong-induction {φ = b ↦ ∀{a} → ∃(Gcd a b)} base step {b}{a} where
  base : ∀{a} → ∃(Gcd a 𝟎)
  base{a} = [∃]-intro a ⦃ Gcd-base ⦄

  step : ∀{i} → (∀{j} → (j ≤ i) → ∀{a} → ∃(Gcd a j)) → ∀{a} → ∃(Gcd a (𝐒(i)))
  step {i} prev {a} with [≥]-or-[<] {a}{𝐒(i)}
  ... | [∨]-introₗ ia = [∃]-map-proof (Gcd-step ia ∘ Gcd-swap) (prev{a mod 𝐒(i)} ([≤]-without-[𝐒] (mod-maxᵣ{a}{𝐒(i)})) {𝐒(i)})
  ... | [∨]-introᵣ (succ ai) = [∃]-map-proof Gcd-swap(prev {a} ai {𝐒(i)})

Gcd-gcdFold : ∀{a b}{ℓ}{T : Type{ℓ}}{f}{g}{x : T} → Gcd a b (Tuple.left(gcdFold f g x a b))
Gcd-gcdFold{a}{b}{f = f}{g}{x} = ℕ-strong-induction {φ = b ↦ ∀{a} → Gcd a b (Tuple.left(gcdFold f g x a b))} base step {b}{a} where
  base : ∀{a} → Gcd a 𝟎 (Tuple.left(gcdFold f g x a 𝟎))
  base{a} = Gcd-base

  step : ∀{i} → (∀{j} → (j ≤ i) → ∀{a} → Gcd a j (Tuple.left(gcdFold f g x a j))) → ∀{a} → Gcd a (𝐒(i)) (Tuple.left(gcdFold f g x a (𝐒(i))))
  step {i} prev {a} with [≥]-or-[<] {a}{𝐒(i)}
  ... | [∨]-introₗ ia = (Gcd-step ia ∘ Gcd-swap) (prev{a mod 𝐒(i)} ([≤]-without-[𝐒] (mod-maxᵣ{a}{𝐒(i)})) {𝐒(i)})
  ... | [∨]-introᵣ (succ ai) = Gcd-swap(prev {a} ai {𝐒(i)})

-- Usage: This allows the transferrence of proofs between `Gcd` and `gcd`. It is sometimes easier to prove properties by using `Gcd` first and then transfering them so that the proofs also hold for `gcd`.
Gcd-gcdFold-value : ∀{a b D}{ℓ}{T : Type{ℓ}}{f}{g}{x : T} → (Gcd a b D) ↔ (Tuple.left(gcdFold f g x a b) ≡ D)
Gcd-gcdFold-value = [↔]-intro (\{[≡]-intro → Gcd-gcdFold}) (Gcd-unique Gcd-gcdFold)

Gcd-gcd : Gcd a b (gcd a b)
Gcd-gcd = Gcd-gcdFold

Gcd-gcd-value : (Gcd a b d) ↔ (gcd a b ≡ d)
Gcd-gcd-value = Gcd-gcdFold-value
