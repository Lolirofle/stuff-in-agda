module Numeral.Natural.Function.GreatestCommonDivisor where

import Lvl
open import Data
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Classical
open import Type

{-# TERMINATING #-}
gcdFold : ∀{ℓ}{T : Type{ℓ}} → ((a : ℕ) → (b : ℕ) → (a ≥ b) → (b > 𝟎) → T → T → T) → ((a : ℕ) → (b : ℕ) → (a < b) → (b > 𝟎) → T → T → T) → T → ℕ → ℕ → (ℕ ⨯ T)
gcdFold f g x (a)(𝟎) = (a , x)
gcdFold f g x (a)(𝐒(b)) with [≥]-or-[<] {a}{𝐒(b)}
... | [∨]-introₗ ab = Tuple.mapRight (f a (𝐒(b)) ab [<]-minimum x) (gcdFold f g x (𝐒(b))(a mod 𝐒(b)))
... | [∨]-introᵣ ba = Tuple.mapRight (g a (𝐒(b)) ba [<]-minimum x) (gcdFold f g x (𝐒(b))(a))

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

-- TODO: Does not always work in the naturals? https://math.stackexchange.com/questions/237372/finding-positive-b%C3%A9zout-coefficients https://math.stackexchange.com/questions/1230224/positive-solutions-of-893x-2432y-19?rq=1
gcdExt : ℕ → ℕ → (ℕ ⨯ ℕ ⨯ ℕ)
gcdExt a b = gcdFold(\{a (𝐒 b) _ [<]-minimum _ (x , y) → (y , x −₀ ((a ⌊/⌋ 𝐒(b)) ⋅ y))}) (\_ _ _ _ _ → Tuple.swap) (1 , 0) a b

lcm : ℕ → ℕ → ℕ
lcm(a)(b) = (a ⋅ b) ⌊/⌋₀ gcd(a)(b)

-- `Gcd a b D` means that `D` is a divisor of both `a` and `b`, and the greatest one of them.
record Gcd (a b D : ℕ) : Type{Lvl.𝟎} where
  constructor intro
  field
    divides-left  : (D ∣ a)
    divides-right : (D ∣ b)
    maximum       : ∀{d} → (d ∣ a) → (d ∣ b) → (d ∣ D)

open import Functional
open import Logic.Predicate
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Relator.Properties
open import Structure.Setoid.Uniqueness
open import Syntax.Function

Gcd-unique : ∀{a b} → Unique(Gcd a b)
Gcd-unique p q = antisymmetry(_∣_)(_≡_)
  (Gcd.maximum q (Gcd.divides-left p) (Gcd.divides-right p))
  (Gcd.maximum p (Gcd.divides-left q) (Gcd.divides-right q))

Gcd-base : ∀{a} → Gcd(a)(𝟎)(a)
Gcd.divides-left  Gcd-base = divides-reflexivity
Gcd.divides-right Gcd-base = Div𝟎
Gcd.maximum       Gcd-base = const

dividing-mod : ∀{a b d} → (d ∣ 𝐒(b)) → (d ∣ a) ↔ (d ∣ a mod 𝐒(b))
dividing-mod {a}{b}{d} db = [↔]-intro (l db) (r db) where
  open import Numeral.Natural.Oper.DivMod.Proofs
  open import Structure.Function.Domain
  open import Structure.Operator.Properties
  open import Structure.Operator.Proofs.Util
  open import Syntax.Transitivity

  l : ∀{a b d} → (d ∣ 𝐒(b)) → (d ∣ a) ← (d ∣ (a mod₀ 𝐒(b)))
  l {a}{b}{𝟎}    db dmod with () ← [0]-only-divides-[0] db
  l {a}{b}{𝐒(d)} db dmod
    with [∃]-intro (𝐒(n)) ⦃ dnb ⦄  ← divides-elim db
    with [∃]-intro m     ⦃ dmmod ⦄ ← divides-elim dmod
    = divides-intro ([∃]-intro (((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ 𝐒(n)) + m) ⦃ p ⦄) where
    p : (𝐒(d) ⋅ (((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ 𝐒(n)) + m) ≡ a)
    p =
      𝐒(d) ⋅ (((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ 𝐒(n)) + m)                     🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(_+_) {𝐒(d)}{(a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ 𝐒(n)}{m} ]
      (𝐒(d) ⋅ ((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ 𝐒(n))) + (𝐒(d) ⋅ m)            🝖[ _≡_ ]-[ [≡]-with(_+ (𝐒(d) ⋅ m)) (One.commuteₗ-assocᵣ {a = 𝐒(d)}{a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))}{𝐒(n)}) ]
      ((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ (𝐒(d) ⋅ 𝐒(n))) + (𝐒(d) ⋅ m)            🝖[ _≡_ ]-[ [≡]-with(((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ (𝐒(d) ⋅ 𝐒(n))) +_) dmmod ]
      ((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ (𝐒(d) ⋅ 𝐒(n))) + (a mod 𝐒(b))          🝖[ _≡_ ]-[ [≡]-with(expr ↦ ((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ (𝐒(d) ⋅ 𝐒(n))) + (a mod 𝐒(expr))) (injective(𝐒) dnb) ]-sym
      ((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ (𝐒(d) ⋅ 𝐒(n))) + (a mod (𝐒(d) ⋅ 𝐒(n))) 🝖[ _≡_ ]-[ [⌊/⌋][mod]-is-division-with-remainder {a}{d + 𝐒(d) ⋅ n} ]
      a                                                               🝖-end

  r : ∀{a b d} → (d ∣ 𝐒(b)) → (d ∣ a) → (d ∣ (a mod₀ 𝐒(b)))
  r {a}{b}{𝟎}   db da with [≡]-intro ← [0]-only-divides-[0] da = Div𝟎
  r {a}{b}{𝐒 d} db da
    with [∃]-intro n ⦃ dna ⦄ ← divides-elim da
    with [∃]-intro m ⦃ dmb ⦄ ← divides-elim db
    = divides-intro ([∃]-intro (n mod₀ m) ⦃ p ⦄) where
    p : (𝐒(d) ⋅ (n mod₀ m) ≡ a mod₀ 𝐒(b))
    p =
      𝐒(d) ⋅ (n mod₀ m)          🝖[ _≡_ ]-[ [⋅][mod]-distributivityₗ {n}{m}{𝐒(d)} ]
      (𝐒(d) ⋅ n) mod₀ (𝐒(d) ⋅ m) 🝖[ _≡_ ]-[ [≡]-with(\expr → ((𝐒(d) ⋅ n) mod₀ expr)) dmb ]
      (𝐒(d) ⋅ n) mod₀ 𝐒(b)       🝖[ _≡_ ]-[ [≡]-with(_mod₀ 𝐒(b)) dna ]
      a mod₀ 𝐒(b)                🝖[ _≡_ ]-end

Gcd-step : ∀{a b d} → (a ≥ 𝐒(b)) → Gcd(a mod 𝐒(b))(𝐒(b))(d) → Gcd(a)(𝐒(b))(d)
Gcd.divides-left  (Gcd-step ab p) = [↔]-to-[←] (dividing-mod (Gcd.divides-right p)) (Gcd.divides-left p)
Gcd.divides-right (Gcd-step ab p) = Gcd.divides-right p
Gcd.maximum       (Gcd-step ab p) da db = Gcd.maximum p ([↔]-to-[→] (dividing-mod db) da) db

Gcd-swap : ∀{a b d} → Gcd(a)(b)(d) → Gcd(b)(a)(d)
Gcd.divides-left  (Gcd-swap p) = Gcd.divides-right p
Gcd.divides-right (Gcd-swap p) = Gcd.divides-left p
Gcd.maximum       (Gcd-swap p) = swap(Gcd.maximum p)

-- Note: The construction for the existence is following the same steps as in the definition of the function `gcd`, but unlike `gcd` which does not pass the termination checker, this uses [ℕ]-strong-induction to pass it.
Gcd-existence : ∀{a b} → ∃(Gcd a b)
Gcd-existence{a}{b} = [ℕ]-strong-induction {φ = b ↦ ∀{a} → ∃(Gcd a b)} base step {b}{a} where
  base : ∀{a} → ∃(Gcd a 𝟎)
  base{a} = [∃]-intro a ⦃ Gcd-base ⦄

  step : ∀{i} → (∀{j} → (j ≤ i) → ∀{a} → ∃(Gcd a j)) → ∀{a} → ∃(Gcd a (𝐒(i)))
  step {i} prev {a} with [≥]-or-[<] {a}{𝐒(i)}
  ... | [∨]-introₗ ia = [∃]-map-proof (Gcd-step ia ∘ Gcd-swap) (prev{a mod 𝐒(i)} ([≤]-without-[𝐒] (mod-maxᵣ{a}{𝐒(i)})) {𝐒(i)})
  ... | [∨]-introᵣ ([≤]-with-[𝐒] ⦃ ai ⦄) = [∃]-map-proof Gcd-swap(prev {a} ai {𝐒(i)})

Gcd-gcdFold : ∀{a b}{ℓ}{T : Type{ℓ}}{f}{g}{x : T} → Gcd a b (Tuple.left(gcdFold f g x a b))
Gcd-gcdFold{a}{b}{f = f}{g}{x} = [ℕ]-strong-induction {φ = b ↦ ∀{a} → Gcd a b (Tuple.left(gcdFold f g x a b))} base step {b}{a} where
  base : ∀{a} → Gcd a 𝟎 (Tuple.left(gcdFold f g x a 𝟎))
  base{a} = Gcd-base

  step : ∀{i} → (∀{j} → (j ≤ i) → ∀{a} → Gcd a j (Tuple.left(gcdFold f g x a j))) → ∀{a} → Gcd a (𝐒(i)) (Tuple.left(gcdFold f g x a (𝐒(i))))
  step {i} prev {a} with [≥]-or-[<] {a}{𝐒(i)}
  ... | [∨]-introₗ ia = (Gcd-step ia ∘ Gcd-swap) (prev{a mod 𝐒(i)} ([≤]-without-[𝐒] (mod-maxᵣ{a}{𝐒(i)})) {𝐒(i)})
  ... | [∨]-introᵣ ([≤]-with-[𝐒] ⦃ ai ⦄) = Gcd-swap(prev {a} ai {𝐒(i)})

-- Usage: This allows the transferrence of proofs between `Gcd` and `gcd`. It is sometimes easier to prove properties by using `Gcd` first and then transfering them so that the proofs also hold for `gcd`.
Gcd-gcdFold-value : ∀{a b D}{ℓ}{T : Type{ℓ}}{f}{g}{x : T} → (Gcd a b D) ↔ (Tuple.left(gcdFold f g x a b) ≡ D)
Gcd-gcdFold-value = [↔]-intro (\{[≡]-intro → Gcd-gcdFold}) (Gcd-unique Gcd-gcdFold)

Gcd-gcd : ∀{a b} → Gcd a b (gcd a b)
Gcd-gcd = Gcd-gcdFold

Gcd-gcd-value : ∀{a b D} → (Gcd a b D) ↔ (gcd a b ≡ D)
Gcd-gcd-value = Gcd-gcdFold-value

gcd-gcdExt-equal : ∀{a b} → (gcd a b ≡ Tuple.left(gcdExt a b))
gcd-gcdExt-equal {a}{b} = Gcd-unique {a}{b} Gcd-gcd Gcd-gcdFold

{-
-- TODO: See note in gcdExt
gcd-linearCombination-existence : ∀{a b} → ∃{Obj = ℕ ⨯ ℕ}(\{(x , y) → ((a ⋅ x) + (b ⋅ y) ≡ gcd a b)})
gcd-linearCombination-existence {a}{b} = [ℕ]-strong-induction {φ = b ↦ ∀{a} → ∃{Obj = ℕ ⨯ ℕ}(\{(x , y) → ((a ⋅ x) + (b ⋅ y) ≡ gcd a b)})} base step {b}{a} where
  open import Structure.Operator.Properties
  open import Syntax.Transitivity

  base : ∀{a} → ∃{Obj = ℕ ⨯ ℕ}(\{(x , y) → ((a ⋅ x) + (𝟎 ⋅ y) ≡ gcd a 𝟎)})
  ∃.witness (base {a}) = (1 , 0)
  ∃.proof   (base {a}) = [≡]-intro

  step : ∀{i} → (∀{j} → (j ≤ i) → ∀{a} → ∃{Obj = ℕ ⨯ ℕ}(\{(x , y) → ((a ⋅ x) + (j ⋅ y) ≡ gcd a j)})) → ∀{a} → ∃{Obj = ℕ ⨯ ℕ}(\{(x , y) → ((a ⋅ x) + (𝐒(i) ⋅ y) ≡ gcd a (𝐒(i)))})
  ∃.witness (step {i} prev {a}) with [≥]-or-[<] {a}{𝐒(i)}
  ... | [∨]-introₗ ia with [∃]-intro (x , y) ← prev{a mod 𝐒(i)} ([≤]-without-[𝐒] (mod-maxᵣ {a = a})) {𝐒(i)} = (y , x −₀ ((a ⌊/⌋ 𝐒(i)) ⋅ y))
  ... | [∨]-introᵣ ([≤]-with-[𝐒] ⦃ ai ⦄) with [∃]-intro (x , y) ← prev{a} ai {𝐒(i)} = (y , x)
  ∃.proof (step {i} prev {a}) with [≥]-or-[<] {a}{𝐒(i)}
  ... | [∨]-introₗ ia with [∃]-intro (x , y) ⦃ p ⦄ ← prev{a mod 𝐒(i)} ([≤]-without-[𝐒] (mod-maxᵣ {a = a})) {𝐒(i)} =
    (a ⋅ y) + (𝐒(i) ⋅ (x −₀ ((a ⌊/⌋ 𝐒(i)) ⋅ y)))          🝖[ _≡_ ]-[ {!!} ]
    (a ⋅ y) + ((𝐒(i) ⋅ x) −₀ (𝐒(i) ⋅ ((a ⌊/⌋ 𝐒(i)) ⋅ y))) 🝖[ _≡_ ]-[ {!!} ]
    (a ⋅ y) + ((𝐒(i) ⋅ x) −₀ ((𝐒(i) ⋅ (a ⌊/⌋ 𝐒(i))) ⋅ y)) 🝖[ _≡_ ]-[ {!!} ]
    (a ⋅ y) + ((𝐒(i) ⋅ x) −₀ (((a mod 𝐒(i)) −₀ a) ⋅ y))   🝖[ _≡_ ]-[ {!!} ]
    (𝐒(i) ⋅ x) + ((a ⋅ y) −₀ (((a mod 𝐒(i)) −₀ a) ⋅ y))   🝖[ _≡_ ]-[ {!!} ]
    (𝐒(i) ⋅ x) + ((a −₀ ((a mod 𝐒(i)) −₀ a)) ⋅ y)         🝖[ _≡_ ]-[ {!!} ]
    (𝐒(i) ⋅ x) + ((𝟎 −₀ (a mod 𝐒(i))) ⋅ y)                🝖[ _≡_ ]-[ {!!} ]
    (𝐒(i) ⋅ x) + ((a mod 𝐒(i)) ⋅ (𝟎 −₀ y)                 🝖[ _≡_ ]-[ {!!} ]
    -- TODO: This uses the extended gcd algorithm and yields a negative y

    (𝐒(i) ⋅ x) + ((a mod 𝐒(i)) ⋅ y)                       🝖[ _≡_ ]-[ p ]
    gcd (𝐒(i)) (a mod 𝐒(i))                               🝖-end
  ... | [∨]-introᵣ ([≤]-with-[𝐒] ⦃ ai ⦄) with [∃]-intro (x , y) ⦃ p ⦄ ← prev{a} ai {𝐒(i)} = commutativity(_+_) {a ⋅ y}{𝐒(i) ⋅ x} 🝖 p
-}
