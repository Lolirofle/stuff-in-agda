module Numeral.Natural.Relation.Properties{ℓ} where

import Lvl
open import Data
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Propositional.Theorems{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Proof{ℓ}
open import Numeral.Natural.Relation{ℓ}
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Theorems{ℓ}{Lvl.𝟎}
open import Structure.Operator.Properties{ℓ}{Lvl.𝟎}
open import Structure.Relator.Ordering{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}
open import Type

instance
  [≤]-from-[≡] : ∀{x y : ℕ} → (x ≡ y) → (x ≤ y)
  [≤]-from-[≡] x≡y = [∃]-intro 0 x≡y

instance
  [≤][0]-minimum : ∀{x : ℕ} → (0 ≤ x)
  [≤][0]-minimum {x} = [∃]-intro x [+]-identityₗ
  -- [∃]-intro {ℕ} {\n → 0 + n ≡ x} (x) ([+]-identityₗ)

instance
  [≤]-successor : ∀{a b : ℕ} → (a ≤ b) → (a ≤ 𝐒(b))
  [≤]-successor ([∃]-intro(n) (proof)) = [∃]-intro (𝐒(n)) ([≡]-with-[ 𝐒 ] proof)
  -- a + n ≡ b //f
  -- a + ? ≡ 𝐒(b) //What value works if f?
  -- a + 𝐒(n) ≡ 𝐒(b)
  -- 𝐒(a + n) ≡ 𝐒(b) //[≡]-with-[ 𝐒 ] f

instance
  [≤]-predecessor : ∀{a b : ℕ} → (𝐒(a) ≤ b) → (a ≤ b)
  [≤]-predecessor ([∃]-intro(n) (proof)) = [∃]-intro (𝐒(n)) (proof)

[ℕ]-strong-induction : ∀{b : ℕ}{φ : ℕ → Stmt} → (∀(i : ℕ) → (i ≤ b) → φ(i)) → (∀(i : ℕ) → φ(i) → φ(𝐒(i))) → (∀{n} → φ(n))
[ℕ]-strong-induction {𝟎}   {φ} (base) (next) = [ℕ]-induction {φ} (base(𝟎) ([∃]-intro(𝟎)([≡]-intro))) (next)
[ℕ]-strong-induction {𝐒(b)}{φ} (base) (next) = [ℕ]-strong-induction {b}{φ} (base-prev) (next) where
  base-prev : ∀(i : ℕ) → (i ≤ b) → φ(i)
  base-prev(𝟎)    (proof) = base(𝟎) ([≤][0]-minimum)
  base-prev(𝐒(i)) (proof) = next(i) (base-prev(i) ([≤]-predecessor {i}{b} proof))

instance
  [≤]-with-[𝐒] : ∀{a b : ℕ} → (a ≤ b) → (𝐒(a) ≤ 𝐒(b))
  [≤]-with-[𝐒] {a} {b} ([∃]-intro n f) =
    [∃]-intro
      (n)
      (
        ([+1]-commutativity {a} {n}) -- 𝐒(a)+n = a+𝐒(n)
        🝖 ([≡]-with-[ 𝐒 ] f) -- 𝐒(a+n)=a+𝐒(n) = 𝐒(b)
      )

instance
  [≤]-without-[𝐒] : ∀{a b : ℕ} → (a ≤ b) ← (𝐒(a) ≤ 𝐒(b))
  [≤]-without-[𝐒] {𝟎}   {b}    (_)                    = [≤][0]-minimum
  [≤]-without-[𝐒] {𝐒(a)}{𝟎}    ()
  [≤]-without-[𝐒] {𝐒(a)}{𝐒(b)} ([∃]-intro(n) (proof)) = [≤]-with-[𝐒] {a}{b} ([≤]-without-[𝐒] {a}{b} ([∃]-intro(n) ([𝐒]-injectivity proof)))

instance
  [≤]-transitivity : Transitivity (_≤_)
  transitivity{{[≤]-transitivity}} {a}{b}{c} (([∃]-intro n₁ a+n₁≡b),([∃]-intro n₂ b+n₂≡c)) =
    [∃]-intro
      (n₁ + n₂)
      (
        (symmetry ([+]-associativity {a} {n₁} {n₂})) -- a+(n₁+n₂) = (a+n₁)+n₂
        🝖 ([≡]-with-[(expr ↦ expr + n₂)] (a+n₁≡b)) -- (a+n₁)+n₂ = b+n₂
        🝖 (b+n₂≡c) -- b+n₂ = c
      ) -- a+(n₁+n₂) = c

instance
  [≤]-reflexivity : Reflexivity (_≤_)
  reflexivity{{[≤]-reflexivity}} = [≤]-from-[≡] [≡]-intro

instance
  [≤]-antisymmetry : Antisymmetry (_≤_) (_≡_)
  antisymmetry{{[≤]-antisymmetry}} {a} {b} (([∃]-intro n₁ a+n₁≡b) , ([∃]-intro n₂ b+n₂≡a)) = [≡]-elimᵣ n₁≡0 {n ↦ (a + n ≡ b)} a+n₁≡b where
    n₁+n₂≡0 : ((n₁ + n₂) ≡ 0)
    n₁+n₂≡0 =
      [+]-injectiveᵣ(
        (symmetry([+]-associativity {a} {n₁} {n₂}))
        🝖 ([≡]-with-[(expr ↦ expr + n₂)] a+n₁≡b)
        🝖 b+n₂≡a
      )
    n₁≡0 : (n₁ ≡ 0)
    n₁≡0 = [+]-sum-is-0ₗ {n₁} {n₂} n₁+n₂≡0
  -- a+n₁ = b
  -- (a+n₁)+n₂ = b+n₂
  -- (a+n₁)+n₂ = a
  -- a+(n₁+n₂) = a
  -- a+(n₁+n₂) = a+0
  -- n₁+n₂ = 0
  -- a = b

instance
  [≤]-weakPartialOrder : Weak.PartialOrder (_≤_) (_≡_)
  [≤]-weakPartialOrder = record{
      antisymmetry = [≤]-antisymmetry;
      transitivity = [≤]-transitivity;
      reflexivity  = [≤]-reflexivity
    }

instance
  [<][0]-minimum : ∀{x : ℕ} → (0 < 𝐒(x))
  [<][0]-minimum {x} = [≤]-with-[𝐒] {0} ([≤][0]-minimum)

-- TODO
instance
  postulate [≮]-is-[≥] : ∀{a b : ℕ} → ¬(a < b) → (a ≥ b)
  postulate [≥]-is-[≮] : ∀{a b : ℕ} → ¬(a < b) ← (a ≥ b)

instance
  postulate [≯]-is-[≤] : ∀{a b : ℕ} → ¬(a > b) → (a ≤ b)
  postulate [≤]-is-[≯] : ∀{a b : ℕ} → ¬(a > b) ← (a ≤ b)

instance
  postulate [≰]-is-[>] : ∀{a b : ℕ} → ¬(a ≤ b) → (a > b)
  postulate [>]-is-[≰] : ∀{a b : ℕ} → ¬(a ≤ b) ← (a > b)

instance
  postulate [≱]-is-[<] : ∀{a b : ℕ} → ¬(a ≥ b) → (a < b)
  postulate [<]-is-[≱] : ∀{a b : ℕ} → ¬(a ≥ b) ← (a < b)

instance
  [ℕ]-zero-or-nonzero : ∀{n} → (n ≡ 𝟎)∨(n ≢ 𝟎)
  [ℕ]-zero-or-nonzero {𝟎}    = [∨]-introₗ [≡]-intro
  [ℕ]-zero-or-nonzero {𝐒(_)} = [∨]-introᵣ \()

instance
  [ℕ]-eq-or-not : ∀{a b} → (a ≡ b)∨(a ≢ b)
  [ℕ]-eq-or-not {𝟎}   {𝟎}    = [∨]-introₗ [≡]-intro
  [ℕ]-eq-or-not {𝟎}   {𝐒(_)} = [∨]-introᵣ \()
  [ℕ]-eq-or-not {𝐒(_)}{𝟎}    = [∨]-introᵣ \()
  [ℕ]-eq-or-not {𝐒(a)}{𝐒(b)} = [∨]-elim ([∨]-introₗ ∘ [≡]-with-[ 𝐒 ]) ([∨]-introᵣ ∘ (contrapositiveᵣ [𝐒]-injectivity)) ([ℕ]-eq-or-not {a}{b})
