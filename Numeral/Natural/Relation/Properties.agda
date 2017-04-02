module Numeral.Natural.Relation.Properties where

import Level as Lvl
open import Data
open import Functional
open import Logic(Lvl.𝟎)
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties
open import Numeral.Natural.Relation
open import Relator.Equals(Lvl.𝟎)
open import Structure.Operator.Properties(Lvl.𝟎)
open import Structure.Relator.Ordering(Lvl.𝟎)
open import Structure.Relator.Properties(Lvl.𝟎)
open import Type

[≤]-from-[≡] : ∀{x y : ℕ} → (x ≡ y) → (x ≤ y)
[≤]-from-[≡] x≡y = [∃]-intro 0 x≡y

[≤][0]-minimum : ∀{x : ℕ} → (0 ≤ x)
[≤][0]-minimum {x} = [∃]-intro x [+]-identityₗ
-- [∃]-intro {ℕ} {\n → 0 + n ≡ x} (x) ([+]-identityₗ)

[≤]-successor : ∀{a b : ℕ} → (a ≤ b) → (a ≤ 𝐒(b))
[≤]-successor ([∃]-intro n f) = [∃]-intro (𝐒(n)) ([≡]-with-[ 𝐒 ] f)
-- a + n ≡ b //f
-- a + ? ≡ 𝐒(b) //What value works if f?
-- a + 𝐒(n) ≡ 𝐒(b)
-- 𝐒(a + n) ≡ 𝐒(b) //[≡]-with-[ 𝐒 ] f

-- [≤]-predecessor : ∀{a b : ℕ} → (𝐒(a) ≤ b) → (a ≤ b)
-- [≤]-predecessor ([∃]-intro n f) = [∃]-intro (𝐒(n)) ([≡]-with-[ 𝐒 ] f)

[≤]-with-[𝐒] : ∀{a b : ℕ} → (a ≤ b) → (𝐒(a) ≤ 𝐒(b))
[≤]-with-[𝐒] {a} {b} ([∃]-intro n f) =
  [∃]-intro
    (n)
    ([≡]-transitivity([∧]-intro
      ([+1]-commutativity {a} {n}) -- 𝐒(a)+n = a+𝐒(n)
      ([≡]-with-[ 𝐒 ] f) -- 𝐒(a+n)=a+𝐒(n) = 𝐒(b)
    ))

[≤]-transitivity : Transitivity (_≤_)
[≤]-transitivity {a} {b} {c} (([∃]-intro n₁ a+n₁≡b),([∃]-intro n₂ b+n₂≡c)) =
  [∃]-intro
    (n₁ + n₂)
    ([≡]-transitivity([∧]-intro
      ([≡]-transitivity([∧]-intro
        ([≡]-symmetry ([+]-associativity {a} {n₁} {n₂})) -- a+(n₁+n₂) = (a+n₁)+n₂
        ([≡]-with-[(expr ↦ expr + n₂)] (a+n₁≡b)) -- (a+n₁)+n₂ = b+n₂
      ))
      (b+n₂≡c) -- b+n₂ = c
    )) -- a+(n₁+n₂) = c

[≤]-reflexivity : Reflexivity (_≤_)
[≤]-reflexivity = [≤]-from-[≡] [≡]-intro

[≤]-antisymmetry : Antisymmetry (_≤_) (_≡_)
[≤]-antisymmetry {a} {b} (([∃]-intro n₁ a+n₁≡b) , ([∃]-intro n₂ b+n₂≡a)) = [≡]-substitution (n ↦ (a + n ≡ b)) n₁≡0 a+n₁≡b where
  n₁+n₂≡0 : ((n₁ + n₂) ≡ 0)
  n₁+n₂≡0 =
    [+]-injectiveᵣ(
      [≡]-transitivity([∧]-intro
        ([≡]-symmetry([+]-associativity {a} {n₁} {n₂}))
        ([≡]-transitivity([∧]-intro
          ([≡]-with-[(expr ↦ expr + n₂)]
            a+n₁≡b
          )
          b+n₂≡a
        ))
      )
    )
  n₁≡0 : (n₁ ≡ 0)
  n₁≡0 = [+]-sum-is-0 {n₁} {n₂} n₁+n₂≡0
-- a+n₁ = b
-- (a+n₁)+n₂ = b+n₂
-- (a+n₁)+n₂ = a
-- a+(n₁+n₂) = a
-- a+(n₁+n₂) = a+0
-- n₁+n₂ = 0
-- a = b

[≤]-weakPartialOrder : WeakPartialOrder (_≤_) (_≡_)
[≤]-weakPartialOrder = record{
    antisymmetry = [≤]-antisymmetry;
    transitivity = [≤]-transitivity;
    reflexivity  = [≤]-reflexivity
  }
