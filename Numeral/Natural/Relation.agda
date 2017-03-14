module Numeral.Natural.Relation where

import Level as Lvl
open import Logic
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Relator.Equals Lvl.𝟎

[ℕ]-induction : {X : ℕ → Set} → X(𝟎) → ((i : ℕ) → X(i) → X(𝐒(i))) → (n : ℕ) → X(n)
[ℕ]-induction base next 𝟎 = base
[ℕ]-induction base next (𝐒(n)) = next(n)([ℕ]-induction base next n)

[+]-identityₗ : ∀ {x} → (0 + x) ≡ x
[+]-identityₗ {x} = [ℕ]-induction base next x where
  base : ((0 + 0) ≡ 0)
  base = [≡]-intro

  next : (i : ℕ) → ((0 + i) ≡ i) → ((0 + 𝐒(i)) ≡ 𝐒(i))
  next _ = [≡]-with-[ 𝐒 ]

[+]-identityᵣ : ∀ {x} → (x + 0) ≡ x
[+]-identityᵣ {x} = [ℕ]-induction base next x where
  base : ((0 + 0) ≡ 0)
  base = [≡]-intro

  next : (i : ℕ) → ((i + 0) ≡ i) → ((𝐒(i) + 0) ≡ 𝐒(i))
  next _ = [≡]-with-[ 𝐒 ]

[+]-associativity : ∀ {x y z} → ((x + y) + z) ≡ (x + (y + z))
[+]-associativity {x} {y} {z} = [ℕ]-induction (base x y) (next x y) z where
  base : ∀ (x y : ℕ) → ((x + y) + 0) ≡ (x + (y + 0))
  base _ _ = [≡]-intro

  next : ∀ (x y : ℕ) → (i : ℕ) → ((x + y) + i) ≡ (x + (y + i)) → ((x + y) + 𝐒(i)) ≡ (x + (y + 𝐒(i)))
  next _ _ _ = [≡]-with-[ 𝐒 ]

-- TODO
-- [+]-commutativity : ∀ {x y} → (x + y) ≡ (y + x)
-- [+]-commutativity {x} {y} = [ℕ]-induction (base x) (next x) y where
--   base : ∀ (x : ℕ) → (0 + x) ≡ (x + 0)
--   base _ = [≡]-transitivity([∧]-intro [+]-identityₗ ([≡]-symmetry [+]-identityᵣ))
-- 
--   next : ∀ (x : ℕ) → (i : ℕ) → (i + x) ≡ (x + i) → (𝐒(i) + x) ≡ (x + 𝐒(i))
--   next _ _ = 


-- [⋅]-identity : ∀ {x} → (1 ⋅ x) ≡ x
-- [⋅]-identity {x} = [ℕ]-induction base next x where
--   base : ((1 ⋅ 0) ≡ 0)
--   base = [≡]-reflexivity
-- 
--   next : (i : ℕ) → ((1 ⋅ i) ≡ i) → ((1 ⋅ 𝐒(i)) ≡ 𝐒(i))
--   next _ stmt = [≡]-reflexivity

-- [⋅]-commutativity : ∀ {x y} → (x ⋅ y) ≡ (y ⋅ x)
-- [⋅]-associativity : ∀ {x y z} → ((x ⋅ y) ⋅ z) ≡ (x ⋅ (y ⋅ z))
-- [⋅]-absorber0 : ∀ {x} → (0 ⋅ x) ≡ 0

-- [⋅][+]-distributivity : ∀ {x y z} → (x ⋅ (y + z)) ≡ (x ⋅ y) + (x ⋅ z)

-- [+]-identity : {x : ℕ} → (0 + x) ≡ x -- TODO: How to prove? Can it be proven?
-- [+]-identity {x} = [≡]-reflexivity {x}

-- Divisibility
data Even : ℕ → Set where
  Even0 : Even 𝟎
  Even𝐒 : {x : ℕ} → (Even x) → (Even(𝐒(𝐒(x))))

data Odd : ℕ → Set where
  Odd0 : Odd (𝐒(𝟎))
  Odd𝐒 : {x : ℕ} → (Odd x) → (Odd(𝐒(𝐒(x))))

data _divides_ : ℕ → ℕ → Set where
  Div0 : {x : ℕ} → x divides 𝟎
  Div𝐒 : {x : ℕ} → {y : ℕ} → (x divides y) → (x divides (x + y))

data _divides_withRemainder_ : ℕ → ℕ → ℕ → Set where
  DivRem0 : {x : ℕ} →{r : ℕ} → x divides r withRemainder r
  DivRem𝐒 : {x : ℕ} → {y : ℕ} → {r : ℕ} → (x divides y withRemainder r) → (x divides (x + y) withRemainder r)
