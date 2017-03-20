module Numeral.Natural.Oper.Properties where

import Level as Lvl
open import Data
open import Functional
open import Logic(Lvl.𝟎)
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Relator.Equals(Lvl.𝟎)
open import Structure.Function.Domain(Lvl.𝟎)
open import Structure.Operator.Properties(Lvl.𝟎)
open import Structure.Relator.Properties(Lvl.𝟎)

instance
  [+]-identityₗ : Identityₗ (_+_) (0)
  [+]-identityₗ {x} = [ℕ]-induction base next x where
    base : ((0 + 0) ≡ 0)
    base = [≡]-intro

    next : ∀ (i : ℕ) → ((0 + i) ≡ i) → ((0 + 𝐒(i)) ≡ 𝐒(i))
    next _ = [≡]-with-[ 𝐒 ]

instance
  [+]-identityᵣ : Identityᵣ (_+_) (0)
  [+]-identityᵣ {x} = [ℕ]-induction base next x where
    base : ((0 + 0) ≡ 0)
    base = [≡]-intro

    next : ∀ (i : ℕ) → ((i + 0) ≡ i) → ((𝐒(i) + 0) ≡ 𝐒(i))
    next _ = [≡]-with-[ 𝐒 ]

instance
  [+]-associativity : Associativity (_+_)
  [+]-associativity {x} {y} {z} = [ℕ]-induction (base x y) (next x y) z where
    base : ∀ (x y : ℕ) → ((x + y) + 0) ≡ (x + (y + 0))
    base _ _ = [≡]-intro

    next : ∀ (x y : ℕ) → (i : ℕ) → ((x + y) + i) ≡ (x + (y + i)) → ((x + y) + 𝐒(i)) ≡ (x + (y + 𝐒(i)))
    next _ _ _ = [≡]-with-[ 𝐒 ]

[+1]-commutativity : ∀{x y : ℕ} → (𝐒(x) + y) ≡ (x + 𝐒(y))
[+1]-commutativity {x} {y} = [ℕ]-induction (base x) (next x) y where
  base : ∀ (x : ℕ) → (𝐒(x) + 0) ≡ (x + 𝐒(0))
  base _ = [≡]-intro

  next : ∀ (x : ℕ) → (i : ℕ) → (𝐒(x) + i) ≡ (x + 𝐒(i)) → (𝐒(x) + 𝐒(i)) ≡ (x + 𝐒(𝐒(i)))
  next x i = [≡]-with-[ 𝐒 ]

instance
  [+]-commutativity : Commutativity (_+_)
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

instance
  [⋅]-absorberₗ : Absorberₗ (_⋅_) (0)
  [⋅]-absorberₗ {x} = [ℕ]-induction base next x where
    base : (0 ⋅ 0) ≡ 0
    base = [≡]-reflexivity

    next : ∀ (x : ℕ) → (0 ⋅ x) ≡ 0 → (0 ⋅ 𝐒(x)) ≡ 0
    next _ eq = [≡]-with-[(λ x → 0 + x)] eq

instance
  [⋅]-absorberᵣ : Absorberᵣ (_⋅_) (0)
  [⋅]-absorberᵣ = [≡]-intro

instance
  [⋅]-identityₗ : Identityₗ (_⋅_) (1)
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

instance
  [⋅]-identityᵣ : Identityᵣ (_⋅_) (1)
  [⋅]-identityᵣ = [≡]-intro

-- [⋅][+]-distributivityₗ : ∀{x y z : ℕ} → (x ⋅ (y + z)) ≡ (x ⋅ y) + (x ⋅ z)
-- [⋅][+]-distributivityᵣ : ∀{x y z : ℕ} → ((x + y) ⋅ z) ≡ ((x ⋅ z) + (y ⋅ z))
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

-- [⋅]-associativity : ∀{x y z : ℕ} → ((x ⋅ y) ⋅ z) ≡ (x ⋅ (y ⋅ z))

-- [+]-abelianGroup (_+_) (1) (−_)

-- testAssociativityOfSuccessor1 : ∀{x y} → ((x + 1) + y) ≡ (x + (1 + y))
-- testAssociativityOfSuccessor1 {x} {y} = [+]-associativity {x} {1} {y}

-- testAssociativityOfSuccessor2 : ∀{x y} → (𝐒(x) + y) ≡ (x + (1 + y))
-- testAssociativityOfSuccessor2 {x} {y} = [+]-associativity {x} {1} {y}

instance
  [+]-injectivityₗ : ∀{a} → Injective (λ x → x + a)
  [+]-injectivityₗ {0}    ( x₁+0≡x₂+0 ) = x₁+0≡x₂+0
  [+]-injectivityₗ {𝐒(n)} (x₁+𝐒n≡x₂+𝐒n) = [+]-injectivityₗ {n} ([≡]-with-[ 𝐏 ] x₁+𝐒n≡x₂+𝐒n)

-- TODO: It would be great to be able to chain the transitivity here. Also, rename and generalize this later
commuteBothTemp : ∀{a₁ a₂ b₁ b₂} → (a₁ + a₂ ≡ b₁ + b₂) → (a₂ + a₁ ≡ b₂ + b₁)
commuteBothTemp {a₁} {a₂} {b₁} {b₂} a₁+a₂≡b₁+b₂ =
  ([≡]-transitivity([∧]-intro
    ([≡]-symmetry ([+]-commutativity {a₁} {a₂}))
    ([≡]-transitivity([∧]-intro
      a₁+a₂≡b₁+b₂
      ([+]-commutativity {b₁} {b₂})
    ))
  ))

instance
  [+]-injectiveᵣ : ∀{a} → Injective (λ x → a + x)
  [+]-injectiveᵣ {0}    {x₁} {x₂} ( 0+x₁≡0+x₂ ) = commuteBothTemp {0} {x₁} {0} {x₂} 0+x₁≡0+x₂
  [+]-injectiveᵣ {𝐒(n)} {x₁} {x₂} (𝐒n+x₁≡𝐒n+x₂) =
    [+]-injectiveᵣ {n} (
      commuteBothTemp {x₁} {n} {x₂} {n} ([≡]-with-[ 𝐏 ] (commuteBothTemp {𝐒(n)} {x₁} {𝐒(n)} {x₂} 𝐒n+x₁≡𝐒n+x₂))
    )

[+]-sum-is-0 : ∀{a b} → (a + b ≡ 0) → (a ≡ 0)
[+]-sum-is-0 {a} {0}    a+0≡0 = a+0≡0
[+]-sum-is-0 {a} {𝐒(n)} a+𝐒n≡0 = [+]-sum-is-0 {a} {n} ([≡]-with-[ 𝐏 ] a+𝐒n≡0)
