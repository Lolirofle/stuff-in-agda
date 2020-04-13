module Numeral.Natural.Oper.Modulo.Proofs where

import Lvl
open import Data
open import Data.Boolean.Stmt
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Existence using ([≤]-equivalence)
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Transitivity
open import Type

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- mod'

-- The many steps variant of: `[ r , b ] 𝐒(a') mod' 𝐒(b') = [ 𝐒(r) , b ] a' mod' b'` from the definition.
mod'-ind-step-modulo : ∀{r m' a m} → [ r , m' ] (a + m) mod' m ≡ [ (r + m) , m' ] a mod' 𝟎
mod'-ind-step-modulo {r}{m'}{a}{𝟎}   = [≡]-intro
mod'-ind-step-modulo {r}{m'}{a}{𝐒 m} = mod'-ind-step-modulo {𝐒 r}{m'}{a}{m}
-- mod'-ind-step-modulo {r}{m'}{a}{𝟎} =
--   [ r       , m' ] (a + 𝟎) mod' 𝟎 🝖-[ reflexivity(_≡_) ]
--   [ (r + 𝟎) , m' ] a       mod' 𝟎 🝖-end
-- mod'-ind-step-modulo {r}{m'}{a}{𝐒 m} =
--   [ r          , m' ] (a + 𝐒(m)) mod' 𝐒(m) 🝖-[ reflexivity(_≡_) ]
--   [ r          , m' ] 𝐒(a + m)   mod' 𝐒(m) 🝖-[ reflexivity(_≡_) ]
--   [ 𝐒(r)       , m' ] (a + m)    mod' m    🝖-[ mod'-ind-step-modulo {𝐒 r}{m'}{a}{m} ]
--   [ 𝐒(r + m)   , m' ] a          mod' 𝟎    🝖-[ reflexivity(_≡_) ]
--   [ (r + 𝐒(m)) , m' ] a          mod' 𝟎    🝖-end

-- When states and modulus is zero, the result is zero.
mod'-zero-013 : ∀{a} → ([ 𝟎 , 𝟎 ] a mod' 𝟎 ≡ 𝟎)
mod'-zero-013 {𝟎}    = [≡]-intro
mod'-zero-013 {𝐒(a)} = mod'-zero-013 {a}

mod'-zero-succ-2 : ∀{r b} → ([ r , 𝟎 ] 𝐒(b) mod' b ≡ 𝟎)
mod'-zero-succ-2 {_}{𝟎}    = [≡]-intro
mod'-zero-succ-2 {r}{𝐒(b)} = mod'-zero-succ-2 {𝐒(r)}{b}

-- When the real modulus is 0 and the number is greater than counter modulus, then the result is zero.
[mod₀]-1-3 : ∀{r a b} → ([ r , 𝟎 ] (b + 𝐒(a)) mod' b ≡ 𝟎)
[mod₀]-1-3 {_}   {𝟎}   {𝟎}    = [≡]-intro
[mod₀]-1-3 {𝟎}   {𝐒 a} {𝟎}    = mod'-zero-013 {𝟎 + 𝐒 a}
[mod₀]-1-3 {𝐒 r} {𝐒 a} {𝟎}    = mod'-zero-013 {a}
[mod₀]-1-3 {r}   {𝟎}   {𝐒(b)} = mod'-zero-succ-2 {𝐒 r} {b}
[mod₀]-1-3 {r}   {𝐒(a)}{𝐒(b)} = [mod₀]-1-3 {𝐒(r)}{𝐒(a)}{b}

-- When the number is the temporary modulus, the result is zero.
[mod₀]-2-1 : ∀{r b' b} → ([ r , b' ] 𝐒(b) mod' b) ≡ 𝟎
[mod₀]-2-1 {_}{𝟎}    {𝟎}    = [≡]-intro
[mod₀]-2-1 {r}{𝟎}    {𝐒(b)} = mod'-zero-succ-2 {𝐒 r}{b}
[mod₀]-2-1 {_}{𝐒(_)} {𝟎}    = [≡]-intro
[mod₀]-2-1 {r}{𝐒(b')}{𝐒(b)} = [mod₀]-2-1 {𝐒(r)}{𝐒(b')}{b}
  -- ([ r , 𝐒(b') ] 𝐒(𝐒(b)) mod' 𝐒(b))
  -- ([ 𝐒(r) , 𝐒(b') ] 𝐒(b) mod' b)
  -- ([ _ , 𝐒(b') ] 1 mod' 0)
  -- ([ 𝟎 , 𝐒(b') ] 0 mod' 𝐒(b'))
  -- 0

-- When the 
[mod₀]-2-2 : ∀{r b' a b} → ([ r , b' ] (b + 𝐒(a)) mod' b) ≡ ([ 𝟎 , b' ] a mod' b')
[mod₀]-2-2 {_}{_} {𝟎}   {𝟎}    = [≡]-intro
[mod₀]-2-2 {r}{b'}{𝟎}   {𝐒(b)} = [mod₀]-2-2 {𝐒(r)}{b'}{𝟎}{b}
[mod₀]-2-2 {_}{_} {𝐒(_)}{𝟎}    = [≡]-intro
[mod₀]-2-2 {r}{b'}{𝐒(a)}{𝐒(b)} = [mod₀]-2-2 {𝐒(r)}{b'}{𝐒(a)}{b}

[mod₀]-3-1 : ∀{r b' b} → [ r , b' ] b mod' b ≡ b + r
[mod₀]-3-1 {_}{_} {𝟎}    = [≡]-intro
[mod₀]-3-1 {r}{b'}{𝐒(b)} = [mod₀]-3-1 {𝐒(r)}{b'}{b}

[mod₀]-3-2 : ∀{r b' b c} → [ r , b' ] b mod' (c + b) ≡ b + r
[mod₀]-3-2 {_}{_} {𝟎}   {c} = [≡]-intro
[mod₀]-3-2 {r}{b'}{𝐒(b)}{c} = [mod₀]-3-2 {𝐒(r)}{b'}{b}{c}

mod'-of-modulus-part : ∀{b b' r} → ([ r , b ] 𝐒(b') mod' b' ≡ [ r + b' , b ] 1 mod' 0)
mod'-of-modulus-part {_}{𝟎}    {_} = [≡]-intro
mod'-of-modulus-part {b}{𝐒(b')}{r} = mod'-of-modulus-part{b}{b'}{𝐒(r)}
  -- [ r , 0 ] 𝐒(𝐒(b')) mod' 𝐒(b')
  -- = [ r + 1 , 0 ] 𝐒(b') mod' b'
  -- = ...
  -- = [ r + 𝐒(b') , 0 ] 1 mod' 0

mod'-of-modulus : ∀{b} → [ 0 , b ] 𝐒(b) mod' b ≡ [ 0 , b ] 0 mod' b
mod'-of-modulus{𝟎}    = [≡]-intro
mod'-of-modulus{𝐒(b)} = [mod₀]-2-1 {1} {𝐒 b} {b}

mod'-result-lesser : ∀{r b' a b} → ⦃ _ : (a ≤ b) ⦄ → (([ r , b' ] a mod' b) ≡ r + a)
mod'-result-lesser ⦃ [≤]-minimum ⦄ = [≡]-intro
mod'-result-lesser {r} {b'} {𝐒 a} {𝐒 b} ⦃ [≤]-with-[𝐒] ⦄ = mod'-result-lesser {𝐒 r} {b'} {a} {b}

mod'-maxᵣ : ∀{r b a b'} → ⦃ _ : (b' ≤ b) ⦄ → (([ r , r + b ] a mod' b') ≤ r + b)
mod'-maxᵣ {r} {b} {𝟎} {b'} ⦃ b'b ⦄ = [≤]-of-[+]ₗ
mod'-maxᵣ {r} {𝟎} {𝐒 a} {.0} ⦃ [≤]-minimum ⦄ = mod'-maxᵣ {𝟎} {r} {a} {r} ⦃ reflexivity(_≤_) ⦄
mod'-maxᵣ {r} {𝐒 b} {𝐒 a} {.0} ⦃ [≤]-minimum ⦄ = mod'-maxᵣ {𝟎} {𝐒(r + b)} {a} {𝐒(r + b)} ⦃ reflexivity(_≤_) ⦄
mod'-maxᵣ {r} {𝐒 b} {𝐒 a} {𝐒 b'} ⦃ [≤]-with-[𝐒] {b'} ⦃ p ⦄ ⦄ = mod'-maxᵣ {𝐒 r} {b} {a} {b'} ⦃ p ⦄

{- TODO: Is this not true?
mod'-max2 : ∀{r b a b'} → ⦃ _ : (b' ≤ b) ⦄ → ⦃ _ : (r ≤ b) ⦄ → (([ r , b ] a mod' b') ≤ b)
mod'-max2 {r}{b}{a}{b'} ⦃ b'b ⦄ ⦃ rb ⦄ = [≤]-from-[+] {P = expr ↦ (⦃ _ : r + b' ≤ expr ⦄ → ([ r , expr ] a mod' b') ≤ expr)} {r} (\{bb} → {!!}) ⦃ rb ⦄ ⦃ {!!} ⦄ -- mod'-maxᵣ {b = bb} {a} ⦃ {!!} ⦄
-}

{-
mod'-max2 : ∀{r b a b'} → ⦃ _ : (b' ≤ b) ⦄ → ⦃ _ : (r ≤ b) ⦄ → (([ r , b ] a mod' b') ≤ b)
mod'-max2 {.0} {b} {a} {b'} ⦃ b'b ⦄ ⦃ [≤]-minimum ⦄ = mod'-max {𝟎}{b}{a}{b'} ⦃ b'b ⦄
mod'-max2 {.(𝐒 r)} {.(𝐒 b)} {𝟎} {.0} ⦃ [≤]-minimum ⦄ ⦃ [≤]-with-[𝐒] {r} {b} ⦃ p ⦄ ⦄ = [≤]-with-[𝐒]
mod'-max2 {.(𝐒 r)} {.(𝐒 b)} {𝐒 a} {.0} ⦃ [≤]-minimum ⦄ ⦃ [≤]-with-[𝐒] {r} {b} ⦃ p ⦄ ⦄ = mod'-max2 {𝟎}{𝐒 b}{a}{𝐒 b} ⦃ reflexivity(_≤_) ⦄
mod'-max2 {.(𝐒 r)} {.(𝐒 b)} {𝟎} {.(𝐒 _)} ⦃ [≤]-with-[𝐒] {y = b} ⦄ ⦃ [≤]-with-[𝐒] {r} ⦃ p ⦄ ⦄ = [≤]-with-[𝐒]
mod'-max2 {.(𝐒 r)} {.(𝐒 b)} {𝐒 a} {.(𝐒 b')} ⦃ [≤]-with-[𝐒] {b'} {y = b} ⦃ p ⦄ ⦄ ⦃ [≤]-with-[𝐒] {r} ⦃ q ⦄ ⦄ = mod'-max2 {𝐒(𝐒 r)} {𝐒 b} {a} {b'} ⦃ [≤]-successor p ⦄ ⦃ {!!} ⦄
-}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- mod₀ and mod

mod₀-mod : ∀{a b} → ((a mod₀ 𝐒(b)) ≡ (a mod 𝐒(b)))
mod₀-mod = [≡]-intro

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- mod

mod-of-1 : ∀{a} → (a mod 1 ≡ 0)
mod-of-1 {𝟎}   = [≡]-intro
mod-of-1 {𝐒 a} = mod-of-1{a}

mod-lesser-than-modulus : ∀{a b} → ⦃ _ : a ≤ b ⦄ → (a mod 𝐒(b) ≡ a)
mod-lesser-than-modulus {a} {b} ⦃ ab ⦄ = mod'-result-lesser {0}

mod-maxᵣ : ∀{a b} → ⦃ _ : IsTrue(positive?(b)) ⦄ → (a mod b < b)
mod-maxᵣ {𝟎}   {𝐒 𝟎}    = [≤]-with-[𝐒]
mod-maxᵣ {𝟎}   {𝐒(𝐒 b)} = [≤]-with-[𝐒]
mod-maxᵣ {𝐒 a} {𝐒 𝟎}    = mod-maxᵣ {a}{𝐒 𝟎}
mod-maxᵣ {𝐒 a} {𝐒(𝐒 b)} = [≤]-with-[𝐒] ⦃ mod'-maxᵣ {1}{b}{a}{b} ⦃ reflexivity(_≤_)⦄ ⦄

mod-of-modulus : ∀{b} → (𝐒(b) mod 𝐒(b) ≡ 𝟎)
mod-of-modulus {b} = [mod₀]-2-1 {𝟎}{b}{b}

mod-of-modulus-add : ∀{a b} → ((𝐒(b) + a) mod 𝐒(b) ≡ a mod 𝐒(b))
mod-of-modulus-add {a}{b} = [mod₀]-2-2 {𝟎}{b}{a}{b}

mod-of-modulus-multiple : ∀{a b} → ((𝐒(b) ⋅ a) mod 𝐒(b) ≡ 𝟎)
mod-of-modulus-multiple {𝟎}   {b} = [≡]-intro
mod-of-modulus-multiple {𝐒 a} {b} = mod-of-modulus-add {𝐒(b) ⋅ a}{b} 🝖 mod-of-modulus-multiple {a} {b}

mod-greater-than-modulus : ∀{a b} → ⦃ _ : (a > b) ⦄ → (a mod 𝐒(b) ≡ (a −₀ 𝐒(b)) mod 𝐒(b))
mod-greater-than-modulus {a}{b} ⦃ a>b ⦄ =
  symmetry(_≡_) ([≡]-with(_mod 𝐒(b)) ([↔]-to-[→] [−₀][+]-nullify2 a>b))
  🝖 mod-of-modulus-add {a −₀ 𝐒(b)} {b}

mod-cases : ∀{a b} → (a mod 𝐒(b) ≡ a) ∨ (a mod 𝐒(b) ≡ (a −₀ 𝐒(b)) mod 𝐒(b))
mod-cases {a}{b} with [≤][>]-dichotomy {a}{b}
mod-cases {a}{b} | [∨]-introₗ a≤b = [∨]-introₗ (mod-lesser-than-modulus  ⦃ a≤b ⦄)
mod-cases {a}{b} | [∨]-introᵣ b>a = [∨]-introᵣ (mod-greater-than-modulus ⦃ b>a ⦄)

mod-nested : ∀{a b c} → ⦃ b ≤ c ⦄ → ((a mod 𝐒(b)) mod 𝐒(c) ≡ a mod 𝐒(b))
mod-nested {a} {b} {c} ⦃ bc ⦄ = mod-lesser-than-modulus {a mod 𝐒(b)} ⦃ [≤]-without-[𝐒] (mod-maxᵣ {a}) 🝖 bc ⦄

-- mod-divisibility-cases : ∀{a b} → (a mod 𝐒(b) ≡ a) ∨ ∃(c ↦ (a mod 𝐒(b)) + (𝐒(b) ⋅ c) ≡ a)
-- mod-divisibility-cases {a}{b} = ?

{-
-- {-# TERMINATING #-} -- TODO: Maybe find another way of doing this (But this proof should be correct I think, just that the termination checker cannot detect it?)
mod-zero-cases : ∀{a b} → (a mod 𝐒(b) ≡ 𝟎) → ∃(c ↦ a ≡ 𝐒(b) ⋅ c)
mod-zero-cases {a} {b} ab0 with [≤][>]-dichotomy {a}{b}
mod-zero-cases {a} {b} ab0 | [∨]-introₗ ab = [∃]-intro 𝟎 ⦃ symmetry(_≡_) (mod-lesser-than-modulus ⦃ ab ⦄) 🝖 ab0 ⦄
mod-zero-cases {a} {b} ab0 | [∨]-introᵣ ba with [↔]-to-[←] [≤]-equivalence ba
mod-zero-cases {.(𝐒 (b + p))} {b} ab0 | [∨]-introᵣ ba | [∃]-intro p ⦃ [≡]-intro ⦄ = [∃]-intro (𝐒(c)) ⦃ proof ⦄ where
  curr : ∃(c ↦ p ≡ 𝐒(b) ⋅ c)
  curr =
    mod-zero-cases {p}{b}
    (
      p mod 𝐒(b)          🝖-[ symmetry(_≡_) (mod-of-modulus-add {p}{b}) ]
      (𝐒(b) + p) mod 𝐒(b) 🝖-[ ab0 ]
      𝟎                   🝖-end
    )

  c = [∃]-witness curr

  proof : {!!}
{-mod-zero-cases {a} {b} ab0 | [∨]-introᵣ ba = [∃]-intro (𝐒(c)) ⦃ proof ⦄ where
  prev : ∃(p ↦ 𝐒(b) + p ≡ a)
  prev = [↔]-to-[←] [≤]-equivalence ba

  p = [∃]-witness prev

  curr : ∃(c ↦ p ≡ 𝐒(b) ⋅ c)
  curr =
    mod-zero-cases {p}{b}
    (
      p mod 𝐒(b)          🝖-[ symmetry(_≡_) (mod-of-modulus-add {p}{b}) ]
      (𝐒(b) + p) mod 𝐒(b) 🝖-[ congruence₁(_mod 𝐒(b)) ([∃]-proof prev) ]
      a mod 𝐒(b)          🝖-[ ab0 ]
      𝟎                   🝖-end
    )

  c = [∃]-witness curr

  proof : (a ≡ 𝐒(b) ⋅ 𝐒(c))
  proof =
    a           🝖-[ symmetry(_≡_) ([∃]-proof prev) ]
    𝐒(b) + p    🝖-[ congruence₁(𝐒(b) +_) ([∃]-proof curr) ]
    𝐒(b) ⋅ 𝐒(c) 🝖-end
-}
-}

{-# TERMINATING #-} -- TODO: Write a general induction proof function for the divisibility relation which terminates
mod-divisibility : ∀{a b} → ⦃ _ : IsTrue(positive?(b)) ⦄ → (a mod b ≡ 𝟎) ↔ (b ∣ a)
mod-divisibility {a}{𝐒(b)} = [↔]-intro l r where
  l : ∀{a b} → (a mod 𝐒(b) ≡ 𝟎) ← (𝐒(b) ∣ a)
  l {.0}           {b} Div𝟎              = [≡]-intro
  l {.(𝐒 (b + a))} {b} (Div𝐒 {x = a} ba) = mod-of-modulus-add {a}{b} 🝖 l ba

  r : ∀{a b} → (a mod 𝐒(b) ≡ 𝟎) → (𝐒(b) ∣ a)
  r {a} {b} ab0 with [≤][>]-dichotomy {a}{b}
  r {a} {b} ab0 | [∨]-introₗ ab rewrite symmetry(_≡_) (mod-lesser-than-modulus ⦃ ab ⦄) 🝖 ab0 = Div𝟎
  r {a} {b} ab0 | [∨]-introᵣ ba with [↔]-to-[←] [≤]-equivalence ba
  r {.(𝐒(b) + p)} {b} ab0 | [∨]-introᵣ ba | [∃]-intro p ⦃ [≡]-intro ⦄ =
    divides-with-[+]
      divides-reflexivity
      (r (
        p mod 𝐒(b)          🝖-[ symmetry(_≡_) (mod-of-modulus-add {p}{b}) ]
        (𝐒(b) + p) mod 𝐒(b) 🝖-[ ab0 ]
        𝟎                   🝖-end
      ))

{-
mod-of-𝐒 : ∀{a b} → ((𝐒(a) mod 𝐒(b) ≡ 𝟎) ∨ (𝐒(a) mod 𝐒(b) ≡ 𝐒(a mod 𝐒(b))))
mod-of-𝐒 = {!!}

mod'-test : ∀{r₁ r₂ b a₁ a₂ b'} → (([ r₁ , b ] a₁ mod' b') ≡ ([ r₁ , b ] a₂ mod' b')) → (([ r₂ , b ] a₁ mod' b') ≡ ([ r₂ , b ] a₂ mod' b'))
mod'-test {𝟎} {𝟎} {b} {a₁} {a₂} {b'} eq = eq
mod'-test {𝟎} {𝐒 r₂} {b} {a₁} {a₂} {b'} eq = {!!}
mod'-test {𝐒 r₁} {𝟎} {b} {a₁} {a₂} {b'} eq = {!!}
mod'-test {𝐒 r₁} {𝐒 r₂} {b} {a₁} {a₂} {b'} eq = {!!}

mod-equality-diff : ∀{a b m} → (a mod 𝐒(m) ≡ b mod 𝐒(m)) → ((a 𝄩 b) mod 𝐒(m) ≡ 𝟎)
mod-equality-diff {𝟎}   {𝟎}   {m} ab = [≡]-intro
mod-equality-diff {𝟎}   {𝐒 b} {m} ab = symmetry(_≡_) ab
mod-equality-diff {𝐒 a} {𝟎}   {m} ab = ab
mod-equality-diff {𝐒 a} {𝐒 b} {m} ab = mod-equality-diff {a} {b} {m} {!!}
-}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- mod₀

-- TODO: How can one convert such a proof? mod-to-mod₀-proof : (∀{a} → P(a mod_)) → P(a mod b) → (∀{a b} → P(a mod₀ b))

{-
mod₀-period : ∀{a b} → ((b + a) mod₀ b ≡ a mod₀ b)
mod₀-period {𝟎}   {𝟎}    = [≡]-intro
mod₀-period {𝟎}   {𝐒(b)} = [≡]-intro
mod₀-period {𝐒(a)}{𝟎}    = [≡]-intro
mod₀-period {𝐒(a)}{𝐒(b)} = [mod₀]-2-2 {0}{b}{𝐒(a)}{b}
{-# REWRITE mod₀-period #-}
  -- 𝐒(a) mod₀ 𝐒(b)
  -- [ 0 , b ] 𝐒(a) mod' b
  -- [ 0 , b ] (b + 𝐒(𝐒(a))) mod' b
  -- [ 0 , b ] (𝐒(b) + 𝐒(a)) mod' b
  -- (𝐒(b) + 𝐒(a)) mod₀ 𝐒(b)

-- mod₀-max : ∀{a b} → ((a mod₀ b) ≤ b)
-- mod₀-max {_}{𝟎}    = [≤]-minimum {𝟎}
-- mod₀-max {a}{𝐒(b)} with converseTotal ⦃ [≤]-totality ⦄ {a}{b}
-- ... | [∨]-introₗ a≤b =
--   [≡]-to-[≤] (mod₀-loop {a}{𝐒(b)} ([≤]-with-[𝐒] ⦃ a≤b ⦄))
--   🝖 a≤b
--   🝖 [≤]-of-[𝐒]
-- ... | [∨]-introₗ b<a = ?
  -- b < a
  -- 𝐒b < a
  -- ∃c. 𝐒b+c = a
  -- ((𝐒b+c) mod₀ 𝐒b) = (c mod₀ 𝐒b)
  -- ???
  -- (a mod₀ 𝐒b) ≤ 𝐒b

-- mod₀-max : ∀{a b} → ((a mod₀ 𝐒(b)) < 𝐒(b))
-- mod₀-max : ∀{a b} → ((𝐒(a) mod₀ b) ≤ 𝐒(a mod₀ b))

-- mod₀-eq-predecessor : ∀{a b} → ((𝐒(a) mod₀ b) ≡ 𝐒(c)) → ((a mod₀ b) ≡ c)

mod₀-of-modulus-mult : ∀{a b} → ((b ⋅ a) mod₀ b ≡ 𝟎)
mod₀-of-modulus-mult {𝟎}   {_} = [≡]-intro
mod₀-of-modulus-mult {𝐒(a)}{b} = mod₀-of-modulus-mult {a}{b}

mod₀-of-periods : ∀{a b c} → (((b ⋅ a) + c) mod₀ b ≡ c mod₀ b)
mod₀-of-periods {𝟎}   {_}{_} = [≡]-intro
mod₀-of-periods {𝐒(a)}{b}{c} =
  mod₀-period{(b ⋅ a) + c}{b}
  🝖 mod₀-of-periods {a}{b}{c}

mod₀-subtract-when-zero : ∀{a b} → (a mod₀ b ≡ 𝟎) → ((a −₀ b) mod₀ b ≡ 𝟎)
mod₀-subtract-when-zero {a}{b} proof with [−₀]-cases-commuted{a}{b}
... | [∨]-introᵣ ab0 = congruence₁(_mod₀ b) ab0
... | [∨]-introₗ baba =
  (symmetry(mod₀-period {a −₀ b}{b})    :of: (a −₀ b mod₀ b ≡ (b + (a −₀ b)) mod₀ b))
  🝖 (congruence₁(_mod₀ b) baba             :of: (_ ≡ a mod₀ b))
  🝖 (proof                              :of: (_ ≡ 𝟎))

-- mod₀-divisibility : ∀{a b} → (a mod₀ b ≡ 𝟎) ↔ (b ∣ a)
-- mod₀-divisibility {a}{b} = [↔]-intro (l{a}{b}) (r{a}{b}) where
--   l : ∀{a b} → (b ∣ a) → (a mod₀ b ≡ 𝟎)
--   l{_}       {b}(Div𝟎)           = mod₀-of-0 {b}
--   l{.(b + a)}{b}(Div𝐒{.b}{a} ba) = mod₀-period{a}{b} 🝖 l{a}{b}(ba)
-- 
--   r : ∀{a b} → (a mod₀ b ≡ 𝟎) → (b ∣ a)
--   r{a}{b} ab0 with [−₀]-cases-commuted{a}{b}
--   ... | [∨]-introᵣ ab0 = Div𝟎
--   ... | [∨]-introₗ baba =
--     Div𝐒(r{a −₀ b}{b} (mod₀-subtract-when-zero (ab0)))
--
--   r{𝟎}{b} _     = Div𝟎{b}
--   r{.(b + a2)}{b} amodb = Div𝐒(r{a}{b} (symmetry(mod₀-period) 🝖 amodb))

postulate mod₀-of-𝐒 : ∀{a b} → (𝐒(a) mod₀ b ≡ 𝟎) ∨ (𝐒(a) mod₀ b ≡ 𝐒(a mod₀ b))

-- TODO: Should also be satisfied for b, not just 𝐒(b)
-- mod₀-of-modulus-pre-eq : ∀{a b} → (𝐒(a) mod₀ 𝐒(b) ≡ 𝟎) → (a mod₀ 𝐒(b) ≡ b)
-- mod₀-of-modulus-pre-eq : ∀{a b} → (𝐒(a) mod₀ 𝐒(b) ≡ 𝐒(c)) → (a mod₀ 𝐒(b) ≡ c)

mod₀-𝐒-equality : ∀{a b c} → ((a mod₀ c) ≡ (b mod₀ c)) → ((𝐒(a) mod₀ c) ≡ (𝐒(b) mod₀ c))
mod₀-𝐒-equality {a}{b}{c} proof with mod₀-of-𝐒 {a}{c} | mod₀-of-𝐒 {b}{c}
... | [∨]-introₗ ac | [∨]-introₗ bc = transitivity ac (symmetry bc)
... | [∨]-introₗ ac | [∨]-introᵣ bc = alls where postulate alls : ∀{a} → a
... | [∨]-introᵣ ac | [∨]-introₗ bc = alls where postulate alls : ∀{a} → a
... | [∨]-introᵣ ac | [∨]-introᵣ bc =
  ac
  🝖 congruence₁(𝐒) proof
  🝖 symmetry bc
-- 𝐒(a) mod₀ c ≡ 𝟎
-- 𝐒(b) mod₀ c ≡ 𝐒(b mod₀ c)
-- (a mod₀ c) ≡ (b mod₀ c)
-- 𝐒(a mod₀ c) ≡ 𝐒(b mod₀ c)
-- 𝐒(a mod₀ c) ≡ 𝐒(b) mod₀ c

-- mod₀-𝐒-equality {_}   {_}   {𝟎}       [≡]-intro = [≡]-intro
-- mod₀-𝐒-equality {a}   {b}   {𝐒(𝟎)}    _         = transitivity (mod₀-modulus-1 {𝐒(a)}) (symmetry (mod₀-modulus-1 {𝐒(b)}))
-- mod₀-𝐒-equality {𝟎}   {𝟎}   {𝐒(𝐒(_))} [≡]-intro = [≡]-intro
-- mod₀-𝐒-equality {a}   {b}   {𝐒(𝐒(_))} proof with mod₀-of-𝐒 {}
-- mod₀-𝐒-equality {𝐒(_)}{𝟎}   {𝐒(𝐒(_))} ()
-- mod₀-𝐒-equality {𝐒(_)}{𝐒(_)}{𝐒(𝐒(_))} _ = a where postulate a : ∀{a} → a


postulate mod₀-[+]ₗ-equality : ∀{a b k c} → ((a mod₀ c) ≡ (b mod₀ c)) → (((k + a) mod₀ c) ≡ ((k + b) mod₀ c))
postulate mod₀-[+]ᵣ-equality : ∀{a b k c} → ((a mod₀ c) ≡ (b mod₀ c)) → (((a + k) mod₀ c) ≡ ((b + k) mod₀ c))
postulate mod₀-[+]-equality : ∀{a₁ b₁ a₂ b₂ c} → ((a₁ mod₀ c) ≡ (b₁ mod₀ c)) → ((a₂ mod₀ c) ≡ (b₂ mod₀ c)) → (((a₁ + a₂) mod₀ c) ≡ ((b₁ + b₂) mod₀ c))

postulate mod₀-[⋅]ₗ-equality : ∀{a b k c} → ((a mod₀ c) ≡ (b mod₀ c)) → (((k ⋅ a) mod₀ c) ≡ ((k ⋅ b) mod₀ c))
postulate mod₀-[⋅]ᵣ-equality : ∀{a b k c} → ((a mod₀ c) ≡ (b mod₀ c)) → (((a ⋅ k) mod₀ c) ≡ ((b ⋅ k) mod₀ c))
postulate mod₀-[⋅]-equality : ∀{a₁ b₁ a₂ b₂ c} → ((a₁ mod₀ c) ≡ (b₁ mod₀ c)) → ((a₂ mod₀ c) ≡ (b₂ mod₀ c)) → (((a₁ ⋅ a₂) mod₀ c) ≡ ((b₁ ⋅ b₂) mod₀ c))

-- postulate mod₀-[^]ᵣ-equality : ∀{a b k c} → ((a mod₀ c) ≡ (b mod₀ c)) → (((a ^ k) mod₀ c) ≡ ((b ^ k) mod₀ c))

-- postulate mod₀-[/]ₗ-equality : ∀{a b k c} → ((a mod₀ c) ≡ (b mod₀ c)) → (k ∣ a) → (k ∣ b) → (((k / a) mod₀ c) ≡ ((k / b) mod₀ c))
-- postulate mod₀-[/]ᵣ-equality : ∀{a b k c} → ((a mod₀ c) ≡ (b mod₀ c)) ∧ (k ∣ a) ∧ (k ∣ b) ← (((a / k) mod₀ c) ≡ ((b / k) mod₀ c))

















{-
(𝐒(b) + 𝐒(a)) mod₀ 𝐒(b)
[ 0 , b ] (𝐒(b) + 𝐒(a)) mod' b
[ 0 , b ] 𝐒(𝐒(b + a)) mod' b

b=0:
[ 0 , 𝟎 ] 𝐒(𝐒(𝟎 + a)) mod' 𝟎
[ 0 , 𝟎 ] 𝐒(𝐒(a)) mod' 𝟎
𝟎
[ 0 , 𝟎 ] 𝐒(a) mod' 𝟎

b=𝐒(_):
[ 0 , 𝐒(b) ] 𝐒(𝐒(𝐒(b) + a)) mod' 𝐒(b)
[ 1 , 𝐒(b) ] 𝐒(𝐒(b) + a) mod' b
[ 1 , 𝐒(b) ] 𝐒(𝐒(b + a)) mod' b
?
[ 1 , 𝐒(b) ] a mod' b
[ 0 , 𝐒(b) ] 𝐒(a) mod' 𝐒(b)

[ 0 , b ] 𝐒(a) mod' b
𝐒(a) mod₀ 𝐒(b)
-}

-- _mod₀_ 4 4
-- = [ 0 , 4 ] 4 mod' 3
-- = [ 1 , 4 ] 3 mod' 2
-- = [ 2 , 4 ] 2 mod' 1
-- = [ 3 , 4 ] 1 mod' 0
-- = [ 0 , 4 ] 0 mod' 4


-- _mod₀_ 𝐒(𝐒(a)) 𝐒(𝐒(b))
-- = [ 0 , b ] 𝐒(𝐒(a)) mod' 𝐒(b)
-- = [ 1 , b ] 𝐒(a)    mod' b

{-
((𝐒(a) + 𝐒(b)) mod₀ 𝐒(b))
(𝐒(𝐒(a) + b) mod₀ 𝐒(b))
((𝐒(a) + b) mod₀ b)

(𝐒(a) mod₀ 𝐒(b))
(a mod₀ b)
-}

-- postulate modulo-upper-bound : ∀{a b} → ⦃ proof : (b ≢ 0) ⦄ → ((a mod b) ⦃ proof ⦄ < b)

-- modulo-identity : ∀{a b} → (a < b) → ((a mod₀ b) ≡ a)
-- modulo-identity {_}   {𝟎}    ()
-- modulo-identity {𝟎}   {𝐒(b)} _  = [≡]-intro
-- modulo-identity {𝐒(a)}{𝐒(b)} ([≤]-with-[𝐒] ⦃ ab ⦄) with mod₀-of-𝐒 {a}{𝐒(b)}
-- ... | [∨]-introₗ 𝐒a𝐒b0   = 
-- ... | [∨]-introᵣ 𝐒a𝐒b𝐒ab = 

-- postulate modulo-nested : ∀{a b} → (((a mod₀ b) mod₀ b) ≡ (a mod₀ b))

-- postulate modulo-successor : ∀{a b} → ((𝐒(a) mod₀ b) ≡ (𝐒(a mod₀ b) mod₀ b))

-- postulate modulo-addition : ∀{a₁ a₂ b} → (((a₁ + a₂) mod₀ b) ≡ (((a₁ mod₀ b) + (a₂ mod₀ b)) mod₀ b))

-- postulate modulo-multiplication : ∀{a₁ a₂ b} → (((a₁ ⋅ a₂) mod₀ b) ≡ (((a₁ mod₀ b) ⋅ (a₂ mod₀ b)) mod₀ b))

-- postulate modulo-thing : a −₀ ((a ⌊/₀⌋ b) ⋅ b) ≡ a mod b


{-

module One where
  test0 : (0 mod₀ 1) ≡ 0
  test0 = [≡]-intro

  test1 : (1 mod₀ 1) ≡ 0
  test1 = [≡]-intro

  test2 : (2 mod₀ 1) ≡ 0
  test2 = [≡]-intro

  test3 : (3 mod₀ 1) ≡ 0
  test3 = [≡]-intro

  test4 : (4 mod₀ 1) ≡ 0
  test4 = [≡]-intro

  test5 : (5 mod₀ 1) ≡ 0
  test5 = [≡]-intro

  test6 : (6 mod₀ 1) ≡ 0
  test6 = [≡]-intro

  test7 : (7 mod₀ 1) ≡ 0
  test7 = [≡]-intro

  test8 : (8 mod₀ 1) ≡ 0
  test8 = [≡]-intro

  test9 : (9 mod₀ 1) ≡ 0
  test9 = [≡]-intro

  test10 : (10 mod₀ 1) ≡ 0
  test10 = [≡]-intro

  test11 : (11 mod₀ 1) ≡ 0
  test11 = [≡]-intro

module Two where
  test0 : (0 mod₀ 2) ≡ 0
  test0 = [≡]-intro

  test1 : (1 mod₀ 2) ≡ 1
  test1 = [≡]-intro

  test2 : (2 mod₀ 2) ≡ 0
  test2 = [≡]-intro

  test3 : (3 mod₀ 2) ≡ 1
  test3 = [≡]-intro

  test4 : (4 mod₀ 2) ≡ 0
  test4 = [≡]-intro

  test5 : (5 mod₀ 2) ≡ 1
  test5 = [≡]-intro

  test6 : (6 mod₀ 2) ≡ 0
  test6 = [≡]-intro

  test7 : (7 mod₀ 2) ≡ 1
  test7 = [≡]-intro

  test8 : (8 mod₀ 2) ≡ 0
  test8 = [≡]-intro

  test9 : (9 mod₀ 2) ≡ 1
  test9 = [≡]-intro

  test10 : (10 mod₀ 2) ≡ 0
  test10 = [≡]-intro

  test11 : (11 mod₀ 2) ≡ 1
  test11 = [≡]-intro

module Three where
  test0 : (0 mod₀ 3) ≡ 0
  test0 = [≡]-intro

  test1 : (1 mod₀ 3) ≡ 1
  test1 = [≡]-intro

  test2 : (2 mod₀ 3) ≡ 2
  test2 = [≡]-intro

  test3 : (3 mod₀ 3) ≡ 0
  test3 = [≡]-intro

  test4 : (4 mod₀ 3) ≡ 1
  test4 = [≡]-intro

  test5 : (5 mod₀ 3) ≡ 2
  test5 = [≡]-intro

  test6 : (6 mod₀ 3) ≡ 0
  test6 = [≡]-intro

  test7 : (7 mod₀ 3) ≡ 1
  test7 = [≡]-intro

  test8 : (8 mod₀ 3) ≡ 2
  test8 = [≡]-intro

  test9 : (9 mod₀ 3) ≡ 0
  test9 = [≡]-intro

  test10 : (10 mod₀ 3) ≡ 1
  test10 = [≡]-intro

  test11 : (11 mod₀ 3) ≡ 2
  test11 = [≡]-intro
 -}
-}
