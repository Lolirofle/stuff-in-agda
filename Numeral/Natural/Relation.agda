module Numeral.Natural.Relation where

import Level as Lvl
open import Logic
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Relator.Equals Lvl.𝟎

[ℕ]-induction : {X : ℕ → Set} → X(𝟎) → ((i : ℕ) → X(i) → X(𝐒(i))) → (n : ℕ) → X(n)
[ℕ]-induction base next 𝟎 = base
[ℕ]-induction base next (𝐒(n)) = next(n)([ℕ]-induction base next n)

[+]-identityₗ : ∀ {x : ℕ} → (0 + x) ≡ x
[+]-identityₗ {x} = [ℕ]-induction base next x where
  base : ((0 + 0) ≡ 0)
  base = [≡]-intro

  next : ∀ (i : ℕ) → ((0 + i) ≡ i) → ((0 + 𝐒(i)) ≡ 𝐒(i))
  next _ = [≡]-with-[ 𝐒 ]

[+]-identityᵣ : ∀ {x : ℕ} → (x + 0) ≡ x
[+]-identityᵣ {x} = [ℕ]-induction base next x where
  base : ((0 + 0) ≡ 0)
  base = [≡]-intro

  next : ∀ (i : ℕ) → ((i + 0) ≡ i) → ((𝐒(i) + 0) ≡ 𝐒(i))
  next _ = [≡]-with-[ 𝐒 ]

[+]-associativity : ∀ {x y z : ℕ} → ((x + y) + z) ≡ (x + (y + z))
[+]-associativity {x} {y} {z} = [ℕ]-induction (base x y) (next x y) z where
  base : ∀ (x y : ℕ) → ((x + y) + 0) ≡ (x + (y + 0))
  base _ _ = [≡]-intro

  next : ∀ (x y : ℕ) → (i : ℕ) → ((x + y) + i) ≡ (x + (y + i)) → ((x + y) + 𝐒(i)) ≡ (x + (y + 𝐒(i)))
  next _ _ _ = [≡]-with-[ 𝐒 ]

[+1]-commutativity : ∀ {x y : ℕ} → (𝐒(x) + y) ≡ (x + 𝐒(y))
[+1]-commutativity {x} {y} = [ℕ]-induction (base x) (next x) y where
  base : ∀ (x : ℕ) → (𝐒(x) + 0) ≡ (x + 𝐒(0))
  base _ = [≡]-intro

  next : ∀ (x : ℕ) → (i : ℕ) → (𝐒(x) + i) ≡ (x + 𝐒(i)) → (𝐒(x) + 𝐒(i)) ≡ (x + 𝐒(𝐒(i)))
  next x i = [≡]-with-[ 𝐒 ]

[+]-commutativity : ∀ {x y : ℕ} → (x + y) ≡ (y + x)
[+]-commutativity {x} {y} = [ℕ]-induction (base x) (next x) y where
  base : ∀ (x : ℕ) → (x + 0) ≡ (0 + x)
  base _ = [≡]-symmetry([≡]-transitivity([∧]-intro [+]-identityₗ ([≡]-symmetry [+]-identityᵣ)))
  -- (∀x. 0+x = x) ∧ (∀x. x = x+0) // [∧]-intro [1] [2]
  --   ∀x. 0+x = x //[+]-identityₗ [1]

  --   ∀x. x+0 = x //[+]-identityᵣ
  --   ∀x. x = x+0 //[≡]-symmetry(..) [2]
  -- (∀x. 0+x = x+0) // [≡]-transitivity(..)

  next : ∀ (x i : ℕ) → (x + i) ≡ (i + x) → (x + 𝐒(i)) ≡ (𝐒(i) + x)
  next x i eq =
    [≡]-transitivity([∧]-intro
      ([≡]-with-[ 𝐒 ]
        eq
      )

      ([≡]-symmetry(
        [+1]-commutativity {i} {x}
      ))
    )
  --   ∀x∀i. x+i = i+x //eq
  --   ∀x∀i. 𝐒(x+i) = 𝐒(i+x) //[≡]-with-[ 𝐒 ](..)
  --   ∀x∀i. x+𝐒(i) = i+𝐒(x) //x + 𝐒(y) = 𝐒(x + y) (Definition of _+_) [1]

  --   ∀x∀i. 𝐒(i)+x = i+𝐒(x) //[+1]-commutativity
  --   ∀x∀i. i+𝐒(x) = 𝐒(i)+x //[≡]-symmetry [2]
  -- ∀x∀i. x+𝐒(i) = 𝐒(i)+x //[≡]-transitivity [1] [2]

[⋅]-absorberₗ : ∀ {x} → (0 ⋅ x) ≡ 0
[⋅]-absorberₗ {x} = [ℕ]-induction base next x where
  base : (0 ⋅ 0) ≡ 0
  base = [≡]-reflexivity

  next : ∀ (x : ℕ) → (0 ⋅ x) ≡ 0 → (0 ⋅ 𝐒(x)) ≡ 0
  next _ eq = [≡]-with-[(λ x → 0 + x)] eq

[⋅]-absorberᵣ : ∀ {x : ℕ} → (x ⋅ 0) ≡ 0
[⋅]-absorberᵣ = [≡]-intro

[⋅]-identityₗ : ∀ {x : ℕ} → (1 ⋅ x) ≡ x
[⋅]-identityₗ {x} = [ℕ]-induction base next x where
  base : ((1 ⋅ 0) ≡ 0)
  base = [≡]-reflexivity

  next : (i : ℕ) → ((1 ⋅ i) ≡ i) → ((1 ⋅ 𝐒(i)) ≡ 𝐒(i))
  next i eq =
    [≡]-transitivity([∧]-intro
      ([+]-commutativity {1} {1 ⋅ i})
      ([≡]-with-[ 𝐒 ] eq)
    )
--   1 + 1⋅i = 1⋅i + 1 //[+]-commutativity

--   1⋅i = i //eq
--   𝐒(1⋅i) = 𝐒(i) //[≡]-with[ 𝐒 ] (..)
--   1⋅i + 1 = 𝐒(i) //Definition: (+)
-- 1 + 1⋅i = 𝐒(i)
-- 1 ⋅ 𝐒(i) = 𝐒(i) //1 ⋅ 𝐒(y) = 1 + (1 ⋅ y) (Definition: (⋅))

[⋅]-identityᵣ : ∀ {x : ℕ} → (x ⋅ 1) ≡ x
[⋅]-identityᵣ = [≡]-intro

-- [⋅][+]-distributivityᵣ : ∀ {x y z : ℕ} → ((x + y) ⋅ z) ≡ ((x ⋅ z) + (y ⋅ z))
-- [⋅][+]-distributivityᵣ {x} {y} {z} = [ℕ]-induction (base x y) (next x y) z where
--   base : ∀ (x y : ℕ) → ((x + y) ⋅ 0) ≡ ((x ⋅ 0) + (y ⋅ 0))
--   base _ _ = [≡]-intro

--   next : ∀ (x y z : ℕ) → ((x + y) ⋅ z) ≡ ((x ⋅ z) + (y ⋅ z)) → ((x + y) ⋅ 𝐒(z)) ≡ ((x ⋅ 𝐒(z)) + (y ⋅ 𝐒(z)))
--   next x y z eq = eq
--     -- ((x + y) ⋅ z) ≡ ((x ⋅ z) + (y ⋅ z))
--     -- (x + y) + ((x + y) ⋅ z) = (x + y) + ((x ⋅ z) + (y ⋅ z)) //[≡]-with-[(expr ↦ (x+y) + expr)]
--     -- (x + y) ⋅ 𝐒(z) = (x + y) + ((x ⋅ z) + (y ⋅ z)) // (x + y) ⋅ 𝐒(z) = (x + y) + ((x + y) ⋅ z) (Definition: (⋅))

--     -- (x + y) + ((x ⋅ z) + (y ⋅ z)) = (x + y) + ((x ⋅ z) + (y ⋅ z)) //[≡]-intro
--     -- = x + (y + ((x ⋅ z) + (y ⋅ z))) //[+]-associativity
--     -- = x + ((y + (x ⋅ z)) + (y ⋅ z)) //[+]-associativity
--     -- = x + (((x ⋅ z) + y) + (y ⋅ z)) //[+]-commutativity
--     -- = x + ((x ⋅ z) + (y + (y ⋅ z))) //[+]-associativity
--     -- = (x + (x ⋅ z)) + (y + (y ⋅ z)) //[+]-associativity
--     -- = (x ⋅ 𝐒(z)) + (y ⋅ 𝐒(z)) //Definition: (⋅)

-- [⋅]-associativity : ∀ {x y z : ℕ} → ((x ⋅ y) ⋅ z) ≡ (x ⋅ (y ⋅ z))

-- [⋅][+]-distributivity : ∀ {x y z : ℕ} → (x ⋅ (y + z)) ≡ (x ⋅ y) + (x ⋅ z)



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

-- testAssociativityOfSuccessor1 : ∀ {x y} → ((x + 1) + y) ≡ (x + (1 + y))
-- testAssociativityOfSuccessor1 {x} {y} = [+]-associativity {x} {1} {y}

-- testAssociativityOfSuccessor2 : ∀ {x y} → (𝐒(x) + y) ≡ (x + (1 + y))
-- testAssociativityOfSuccessor2 {x} {y} = [+]-associativity {x} {1} {y}
