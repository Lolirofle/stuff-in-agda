module Numeral.Natural.Relation.Properties where

import Level as Lvl
open import Data
open import Logic(Lvl.𝟎)
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties
open import Numeral.Natural.Relation
open import Relator.Equals(Lvl.𝟎)
open import Structure.Operator.Properties(Lvl.𝟎)
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
        ([≡]-with-[(λ expr → expr + n₂)] (a+n₁≡b)) -- (a+n₁)+n₂ = b+n₂
      ))
      (b+n₂≡c) -- b+n₂ = c
    )) -- a+(n₁+n₂) = c

[≤]-reflexivity : Reflexivity (_≤_)
[≤]-reflexivity = [≤]-from-[≡] [≡]-intro

-- [≤]-antisymmetry : Antisymmetry (_≤_) (_≡_)
-- [≤]-antisymmetry(([∃]-intro n₁ a+n₁≡b) , ([∃]-intro n₂ b+n₂≡a)) =
-- a+(n₁+n₂) = b+(n₁+n₂)
-- a = b
