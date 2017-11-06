module Numeral.Natural.Relation.Properties{ℓ} where

import Lvl
open import Data
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
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
  [≤]-successor ([∃]-intro n f) = [∃]-intro (𝐒(n)) ([≡]-with-[ 𝐒 ] f)
  -- a + n ≡ b //f
  -- a + ? ≡ 𝐒(b) //What value works if f?
  -- a + 𝐒(n) ≡ 𝐒(b)
  -- 𝐒(a + n) ≡ 𝐒(b) //[≡]-with-[ 𝐒 ] f

-- TODO: Implement
instance
  postulate [≤]-predecessor : ∀{a b : ℕ} → (𝐒(a) ≤ b) → (a ≤ b)
  -- [≤]-predecessor ([∃]-intro n f) = [∃]-intro (𝐒(n)) ([≡]-with-[ 𝐒 ] f)

instance
  [≤]-with-[𝐒] : ∀{a b : ℕ} → (a ≤ b) → (𝐒(a) ≤ 𝐒(b))
  [≤]-with-[𝐒] {a} {b} ([∃]-intro n f) =
    [∃]-intro
      (n)
      (
        ([+1]-commutativity {a} {n}) -- 𝐒(a)+n = a+𝐒(n)
        🝖 ([≡]-with-[ 𝐒 ] f) -- 𝐒(a+n)=a+𝐒(n) = 𝐒(b)
      )

-- TODO: Implement
instance
  postulate [≤]-without-[𝐒] : ∀{a b : ℕ} → (a ≤ b) ← (𝐒(a) ≤ 𝐒(b))

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
