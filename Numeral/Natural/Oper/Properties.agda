module Numeral.Natural.Oper.Properties{ℓ} where

import Level as Lvl
open import Data
open import Functional
open import Logic.Propositional{ℓ}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Relation
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Structure.Function.Domain{ℓ}
open import Structure.Operator.Properties{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}

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
    next _ eq = [≡]-with-[(x ↦ 0 + x)] eq

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

instance postulate [⋅][+]-distributivityₗ : ∀{x y z : ℕ} → (x ⋅ (y + z)) ≡ (x ⋅ y) + (x ⋅ z)
instance postulate [⋅][+]-distributivityᵣ : ∀{x y z : ℕ} → ((x + y) ⋅ z) ≡ ((x ⋅ z) + (y ⋅ z))
-- [⋅][+]-distributivityᵣ {x} {y} {z} = [ℕ]-induction (base x y) (next x y) z where
--   base : ∀ (x y : ℕ) → ((x + y) ⋅ 0) ≡ ((x ⋅ 0) + (y ⋅ 0))
--   base _ _ = [≡]-intro
-- 
--   next : ∀ (x y z : ℕ) → ((x + y) ⋅ z) ≡ ((x ⋅ z) + (y ⋅ z)) → ((x + y) ⋅ 𝐒(z)) ≡ ((x ⋅ 𝐒(z)) + (y ⋅ 𝐒(z)))
--   next x y z (x+y)⋅z≡(x⋅z)+(y⋅z) =
--     ([≡]-transitivity([∧]-intro
--       ([≡]-with-[(expr ↦ (x+y) + expr)]
--         (x+y)⋅z≡(x⋅z)+(y⋅z)
--       )
--       [+]-associativity
--     )
    -- ((x + y) ⋅ z) ≡ ((x ⋅ z) + (y ⋅ z))
    -- (x + y) + ((x + y) ⋅ z) = (x + y) + ((x ⋅ z) + (y ⋅ z)) //[≡]-with-[(expr ↦ (x+y) + expr)]
    -- (x + y) ⋅ 𝐒(z) = (x + y) + ((x ⋅ z) + (y ⋅ z)) // (x + y) ⋅ 𝐒(z) = (x + y) + ((x + y) ⋅ z) (Definition: (⋅))

    -- (x + y) + ((x ⋅ z) + (y ⋅ z)) = (x + y) + ((x ⋅ z) + (y ⋅ z)) //[≡]-intro
    -- = x + (y + ((x ⋅ z) + (y ⋅ z))) //[+]-associativity
    -- = x + ((y + (x ⋅ z)) + (y ⋅ z)) //[+]-associativity
    -- = x + (((x ⋅ z) + y) + (y ⋅ z)) //[+]-commutativity
    -- = x + ((x ⋅ z) + (y + (y ⋅ z))) //[+]-associativity
    -- = (x + (x ⋅ z)) + (y + (y ⋅ z)) //[+]-associativity
    -- = (x ⋅ 𝐒(z)) + (y ⋅ 𝐒(z)) //Definition: (⋅)

instance postulate [⋅]-associativity : Associativity (_⋅_)
instance postulate [⋅]-commutativity : Commutativity (_⋅_)

-- testAssociativityOfSuccessor1 : ∀{x y} → ((x + 1) + y) ≡ (x + (1 + y))
-- testAssociativityOfSuccessor1 {x} {y} = [+]-associativity {x} {1} {y}

-- testAssociativityOfSuccessor2 : ∀{x y} → (𝐒(x) + y) ≡ (x + (1 + y))
-- testAssociativityOfSuccessor2 {x} {y} = [+]-associativity {x} {1} {y}

instance
  [𝐒]-injectivity : Injective(𝐒)
  [𝐒]-injectivity {0}    ([≡]-intro) = [≡]-intro
  [𝐒]-injectivity {𝐒(n)} (𝐒x≡𝐒y)     = [≡]-with-[ 𝐏 ] 𝐒x≡𝐒y

instance
  [𝐒]-not-0 : ∀{n} → (𝐒(n) ≢ 𝟎)
  [𝐒]-not-0 ()

instance
  [𝐏][𝐒]-identity : ∀{n} → (𝐏(𝐒(n)) ≡ n)
  [𝐏][𝐒]-identity = [≡]-intro

instance
  [+]-injectivityₗ : ∀{a} → Injective (x ↦ x + a)
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
  [+]-injectiveᵣ : ∀{a} → Injective (x ↦ a + x)
  [+]-injectiveᵣ {0}    {x₁} {x₂} ( 0+x₁≡0+x₂ ) = commuteBothTemp {0} {x₁} {0} {x₂} 0+x₁≡0+x₂
  [+]-injectiveᵣ {𝐒(n)} {x₁} {x₂} (𝐒n+x₁≡𝐒n+x₂) =
    [+]-injectiveᵣ {n} (
      commuteBothTemp {x₁} {n} {x₂} {n} ([≡]-with-[ 𝐏 ] (commuteBothTemp {𝐒(n)} {x₁} {𝐒(n)} {x₂} 𝐒n+x₁≡𝐒n+x₂))
    )

[+]-sum-is-0ₗ : ∀{a b} → (a + b ≡ 0) → (a ≡ 0)
[+]-sum-is-0ₗ {a}{0}    a+0≡0 = a+0≡0
[+]-sum-is-0ₗ {a}{𝐒(n)} a+𝐒n≡0 = [+]-sum-is-0ₗ {a} {n} ([≡]-with-[ 𝐏 ] a+𝐒n≡0)

[+]-sum-is-0ᵣ : ∀{a b} → (a + b ≡ 0) → (b ≡ 0)
[+]-sum-is-0ᵣ {b}{a} (b+a≡0) =
  ([+]-sum-is-0ₗ {a}{b}
    ([≡]-transitivity([∧]-intro
      ([+]-commutativity {a}{b})
      (b+a≡0)
    ))
  )

[+]-sum-is-0 : ∀{a b} → (a + b ≡ 0) → (a ≡ 0)∧(b ≡ 0)
[+]-sum-is-0 {a}{b} (proof) =
  ([∧]-intro
    ([+]-sum-is-0ₗ {a}{b} (proof))
    ([+]-sum-is-0ᵣ {a}{b} (proof))
  )

[⋅]-product-is-0 : ∀{a b} → (a ⋅ b ≡ 0) → ((a ≡ 0)∨(b ≡ 0))
[⋅]-product-is-0 {a}{0} (_) = [∨]-introᵣ ([≡]-intro)
[⋅]-product-is-0 {0}{b} (_) = [∨]-introₗ ([≡]-intro)
[⋅]-product-is-0 {𝐒(a)}{𝐒(b)} (𝐒a⋅𝐒b≡0) =
  ([⊥]-elim
    ([𝐒]-not-0 {(𝐒(a) ⋅ b) + a}
      ([≡]-transitivity([∧]-intro
        ([+]-commutativity {𝐒(a) ⋅ b}{𝐒(a)})
        (𝐒a⋅𝐒b≡0)
      ))
    )
  )
  -- 𝐒a⋅𝐒b = 0 //assumption
  -- 𝐒a+(𝐒a⋅b) = 0 //Definition: (⋅)
  -- (𝐒a⋅b)+𝐒a = 0 //Commutativity (+)
  -- 𝐒((𝐒a⋅b)+a) = 0 //Definition: (+)
  -- ⊥ //∀n. 𝐒(n) ≠ 0
  -- (a = 0) ∨ (b = 0) //[⊥]-elim

-- Also called "The Division Algorithm" or "Euclides Algorithm"
-- TODO: Prove
postulate [/]-uniqueness : ∀{a b} → {{_ : b ≢ 0}} → ∃!{ℕ ⨯ ℕ}(\{(q , r) → ((a ≡ (b ⋅ q) + r)∧(0 ≤ r)∧(r < b))})

instance
  [+]-cancellationᵣ : Cancellationᵣ(_+_)
  [+]-cancellationᵣ {𝟎}    (rel) = rel
  [+]-cancellationᵣ {𝐒(x)} (rel) = [+]-cancellationᵣ {x} ([≡]-with-[ 𝐏 ] rel)

instance
  [+]-cancellationₗ : Cancellationₗ(_+_)
  [+]-cancellationₗ {𝟎}{a}{b} (rel) =
    ([≡]-transitivity([∧]-intro
      ([≡]-transitivity([∧]-intro
        ([≡]-symmetry [+]-identityₗ)
        (rel)
      ))
      ([+]-identityₗ)
    ))
  [+]-cancellationₗ {𝐒(x)}{a}{b} (rel) =
    ([+]-cancellationₗ {x}{a}{b}
      ([≡]-with-[ 𝐏 ]
        ([≡]-transitivity([∧]-intro
          ([≡]-transitivity([∧]-intro
            ([≡]-symmetry ([+1]-commutativity {x}{a}))
            (rel)
          ))
          ([+1]-commutativity {x}{b})
        ))
      )
    )

instance
  [−₀]-negative : ∀{x} → ((0 −₀ x) ≡ 0)
  [−₀]-negative{𝟎}    = [≡]-intro
  [−₀]-negative{𝐒(n)} = [≡]-intro
