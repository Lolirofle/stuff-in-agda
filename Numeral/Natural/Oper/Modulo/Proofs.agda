module Numeral.Natural.Oper.Modulo.Proofs{ℓ} where

import Lvl
open import Logic.Propositional{ℓ}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Proofs{ℓ}
open import Numeral.Natural.Relation{ℓ}
open import Numeral.Natural.Relation.Divisibility{ℓ}
open import Numeral.Natural.Relation.Order{ℓ}
open import Numeral.Natural.Relation.Order.Proofs{ℓ}
open import Numeral.Natural.UnclosedOper
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Proofs{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}
open import Syntax.Function
open import Type

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- mod'

[mod₀]-1-1 : ∀{a} → ([ 𝟎 , 𝟎 ] a mod' 𝟎 ≡ 𝟎)
[mod₀]-1-1 {𝟎}    = [≡]-intro
[mod₀]-1-1 {𝐒(a)} = [mod₀]-1-1 {a}
{-# REWRITE [mod₀]-1-1 #-}

[mod₀]-1-2 : ∀{r b} → ([ r , 𝟎 ] 𝐒(b) mod' b ≡ 𝟎)
[mod₀]-1-2 {_}{𝟎}    = [≡]-intro
[mod₀]-1-2 {r}{𝐒(b)} = [mod₀]-1-2 {𝐒(r)}{b}
{-# REWRITE [mod₀]-1-2 #-}

[mod₀]-1-3 : ∀{r a b} → ([ r , 𝟎 ] (b + 𝐒(a)) mod' b ≡ 𝟎)
[mod₀]-1-3 {_}{𝟎}   {𝟎}    = [≡]-intro
[mod₀]-1-3 {_}{𝐒(_)}{𝟎}    = [≡]-intro
[mod₀]-1-3 {_}{𝟎}   {𝐒(_)} = [≡]-intro
[mod₀]-1-3 {r}{𝐒(a)}{𝐒(b)} = [mod₀]-1-3 {𝐒(r)}{𝐒(a)}{b}
{-# REWRITE [mod₀]-1-3 #-}

-- [mod₀]-2-3 : ∀{r b' b} → ([ r , b' ] 𝐒(𝐒(b)) mod' b) ≡ ([ 𝟎 , b' ] 𝐒(b) mod' b')
[mod₀]-2-1 : ∀{r b' b} → ([ r , b' ] 𝐒(b) mod' b) ≡ 𝟎
[mod₀]-2-1 {_}{𝟎}    {𝟎}    = [≡]-intro
[mod₀]-2-1 {_}{𝟎}    {𝐒(_)} = [≡]-intro
[mod₀]-2-1 {_}{𝐒(_)} {𝟎}    = [≡]-intro
[mod₀]-2-1 {r}{𝐒(b')}{𝐒(b)} = [mod₀]-2-1 {𝐒(r)}{𝐒(b')}{b}
{-# REWRITE [mod₀]-2-1 #-}
  -- ([ r , 𝐒(b') ] 𝐒(𝐒(b)) mod' 𝐒(b))
  -- ([ 𝐒(r) , 𝐒(b') ] 𝐒(b) mod' b)
  -- ([ _ , 𝐒(b') ] 1 mod' 0)
  -- ([ 𝟎 , 𝐒(b') ] 0 mod' 𝐒(b'))
  -- 0

[mod₀]-2-2 : ∀{r b' a b} → ([ r , b' ] (b + 𝐒(a)) mod' b) ≡ ([ 𝟎 , b' ] a mod' b')
[mod₀]-2-2 {_}{_} {𝟎}   {𝟎}    = [≡]-intro
[mod₀]-2-2 {r}{b'}{𝟎}   {𝐒(b)} = [mod₀]-2-2 {r}{b'}{𝟎}{b}
[mod₀]-2-2 {_}{_} {𝐒(_)}{𝟎}    = [≡]-intro
[mod₀]-2-2 {r}{b'}{𝐒(a)}{𝐒(b)} = [mod₀]-2-2 {𝐒(r)}{b'}{𝐒(a)}{b}
{-# REWRITE [mod₀]-2-2 #-}

[mod₀]-3-1 : ∀{r b' b} → [ r , b' ] b mod' b ≡ b + r
[mod₀]-3-1 {_}{_} {𝟎}    = [≡]-intro
[mod₀]-3-1 {r}{b'}{𝐒(b)} = [mod₀]-3-1 {𝐒(r)}{b'}{b}
{-# REWRITE [mod₀]-3-1 #-}

[mod₀]-3-2 : ∀{r b' b c} → [ r , b' ] b mod' (c + b) ≡ b + r
[mod₀]-3-2 {_}{_} {𝟎}   {c} = [≡]-intro
[mod₀]-3-2 {r}{b'}{𝐒(b)}{c} = [mod₀]-3-2 {𝐒(r)}{b'}{b}{c}
{-# REWRITE [mod₀]-3-2 #-}

-- [mod₀]-5 {𝟎}   {𝟎}   {𝟎}   {𝟎}    = [≡]-intro
-- [mod₀]-5 {𝟎}   {𝟎}   {𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀]-5 {𝟎}   {𝟎}   {𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀]-5 {𝟎}   {𝟎}   {𝐒(_)}{𝐒(_)} = [≡]-intro
-- [mod₀]-5 {𝟎}   {𝐒(_)}{𝟎}   {𝟎}    = [≡]-intro
-- [mod₀]-5 {𝟎}   {𝐒(_)}{𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀]-5 {𝟎}   {𝐒(_)}{𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀]-5 {𝟎}   {𝐒(_)}{𝐒(_)}{𝐒(_)} = [≡]-intro
-- [mod₀]-5 {𝐒(_)}{𝟎}   {𝟎}   {𝟎}    = [≡]-intro
-- [mod₀]-5 {𝐒(_)}{𝟎}   {𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀]-5 {𝐒(_)}{𝟎}   {𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀]-5 {𝐒(_)}{𝟎}   {𝐒(_)}{𝐒(_)} = [≡]-intro
-- [mod₀]-5 {𝐒(_)}{𝐒(_)}{𝟎}   {𝟎}    = [≡]-intro
-- [mod₀]-5 {𝐒(_)}{𝐒(_)}{𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀]-5 {𝐒(_)}{𝐒(_)}{𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀]-5 {𝐒(_)}{𝐒(_)}{𝐒(_)}{𝐒(_)} = [≡]-intro

-- [mod₀]-6 : ∀{r b a'} → [ r , b ] a' mod' 𝟎 ≡ [ 𝟎 , b ] a' mod₀ b
-- [mod₀]-6 {𝟎}   {𝟎}   {𝟎}    = [≡]-intro
-- [mod₀]-6 {𝟎}   {𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀]-6 {𝟎}   {𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀]-6 {𝟎}   {𝐒(_)}{𝐒(_)} = [≡]-intro
-- [mod₀]-6 {𝐒(_)}{𝟎}   {𝟎}    = [≡]-intro
-- [mod₀]-6 {𝐒(_)}{𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀]-6 {𝐒(_)}{𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀]-6 {𝐒(_)}{𝐒(_)}{𝐒(_)} = [≡]-intro
-- {-# REWRITE [mod₀]-6 #-}

-- [mod₀]-7 : ∀{r b y} → [ r , b ] y mod' y ≡ 𝟎
-- [mod₀]-7 {𝟎}   {𝟎}   {𝟎}    = [≡]-intro
-- [mod₀]-7 {𝟎}   {𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀]-7 {𝟎}   {𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀]-7 {𝐒(_)}{𝟎}   {𝟎}    = [≡]-intro
-- [mod₀]-7 {𝐒(_)}{𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀]-7 {𝐒(_)}{𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀]-7 {r}   {𝐒(b)}{𝐒(y)} = [mod₀]-7 {𝐒(r)}{𝐒(b)}{y}
-- {-# REWRITE [mod₀]-7 #-}

mod'-of-modulus-part : ∀{b b' r} → ([ r , b ] 𝐒(b') mod' b' ≡ [ r + b' , b ] 1 mod' 0)
mod'-of-modulus-part {_}{𝟎}    {_} = [≡]-intro
mod'-of-modulus-part {b}{𝐒(b')}{r} = mod'-of-modulus-part{b}{b'}{𝐒(r)}
-- {-# REWRITE mod'-of-modulus-part #-}
  -- [ r , 0 ] 𝐒(𝐒(b')) mod' 𝐒(b')
  -- = [ r + 1 , 0 ] 𝐒(b') mod' b'
  -- = ...
  -- = [ r + 𝐒(b') , 0 ] 1 mod' 0

-- mod'-of-modulus : ∀{b} → [ 0 , b ] 𝐒(b) mod' b ≡ [ 0 , b ] 0 mod' b
-- mod'-of-modulus{𝟎}       = [≡]-intro
-- mod'-of-modulus{𝐒(𝟎)}    = [≡]-intro
-- mod'-of-modulus{𝐒(𝐒(b))} = [≡]-intro -- mod'-of-modulus-part{𝐒(𝐒(b))}{𝐒(𝐒(b))}{0} where
-- {-# REWRITE mod'-of-modulus #-}

-- postulate mod'-period-part : ∀{b b' r a} → ([ r , b ] (b' + a) mod' b' ≡ [ r + b' , b ] a mod' 0)
-- mod'-period-part {_}{𝟎}    {_} = [≡]-intro
-- mod'-period-part {b}{𝐒(b')}{r} = mod'-of-modulus-part{b}{b'}{𝐒(r)}
-- {-# REWRITE mod'-period-part #-}
-- postulate all : ∀{a} → a
-- mod'-period-part2 : ∀{b b' r a} → [ r , b ] 𝐒(𝐒(b' + a)) mod' b' ≡ [ r , b' ] 𝐒(a) mod' b'
-- mod'-period-part2 {𝟎}   {𝟎}   {𝟎}   {𝟎}    = [≡]-intro
-- mod'-period-part2 {𝟎}   {𝟎}   {𝟎}   {𝐒(_)} = [≡]-intro
-- mod'-period-part2 {𝟎}   {𝟎}   {𝐒(_)}{𝟎}    = [≡]-intro
-- mod'-period-part2 {𝟎}   {𝟎}   {𝐒(_)}{𝐒(_)} = [≡]-intro
-- mod'-period-part2 {𝟎}   {𝐒(_)}{𝟎}   {𝟎}    = all
-- mod'-period-part2 {𝟎}   {𝐒(_)}{𝟎}   {𝐒(_)} = all
-- mod'-period-part2 {𝟎}   {𝐒(_)}{𝐒(_)}{𝟎}    = all
-- mod'-period-part2 {𝟎}   {𝐒(_)}{𝐒(_)}{𝐒(_)} = all
-- mod'-period-part2 {𝐒(_)}{𝟎}   {𝟎}   {𝟎}    = all
-- mod'-period-part2 {𝐒(_)}{𝟎}   {𝟎}   {𝐒(_)} = all
-- mod'-period-part2 {𝐒(_)}{𝟎}   {𝐒(_)}{𝟎}    = all
-- mod'-period-part2 {𝐒(_)}{𝟎}   {𝐒(_)}{𝐒(_)} = all
-- mod'-period-part2 {𝐒(_)}{𝐒(_)}{𝟎}   {𝟎}    = all
-- mod'-period-part2 {𝐒(_)}{𝐒(_)}{𝟎}   {𝐒(_)} = all
-- mod'-period-part2 {𝐒(_)}{𝐒(_)}{𝐒(_)}{𝟎}    = all
-- mod'-period-part2 {𝐒(_)}{𝐒(_)}{𝐒(_)}{𝐒(_)} = all
-- {-# REWRITE mod'-period-part2 #-}

-- ((𝐒(b) + 𝐒(a)) mod₀ 𝐒(b))
-- = (𝐒(𝐒(b + a)) mod₀ 𝐒(b))
-- = [ 0 , b ] 𝐒(𝐒(b + a)) mod' b
-- = ...
-- = [ 0 , b ] 𝐒(a) mod' b
-- = (𝐒(a) mod₀ 𝐒(b))

-- mod'-period : ∀{a b} → ([ 0 , b ] (𝐒(b) + a) mod' b ≡ [ 0 , b ] a mod' b)
-- mod'-period{𝟎}   {_}    = [≡]-intro
-- mod'-period{𝐒(a)}{𝟎}    = [≡]-intro
-- mod'-period{𝐒(a)}{𝐒(b)} = [≡]-intro
-- {-# REWRITE mod'-period #-}

mod₀-mod : ∀{a b} → ((a mod₀ 𝐒(b)) ≡ (a mod 𝐒(b)) ⦃ [𝐒]-not-0 ⦄)
mod₀-mod = [≡]-intro

-- mod-max : ∀{a b} → ((a mod b) < b)
-- mod-loop : ∀{a b} → (a < b) → ((a mod b) ≡ a)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- mod₀

mod₀-of-0 : ∀{b} → ((0 mod₀ b) ≡ 0)
mod₀-of-0 {𝟎}    = [≡]-intro
mod₀-of-0 {𝐒(b)} = [≡]-intro
{-# REWRITE mod₀-of-0 #-}

mod₀-of-modulus : ∀{b} → ((b mod₀ b) ≡ 0)
mod₀-of-modulus {𝟎}    = [≡]-intro
mod₀-of-modulus {𝐒(b)} = [≡]-intro
{-# REWRITE mod₀-of-modulus #-}

mod₀-modulus-1 : ∀{a} → ((a mod₀ 1) ≡ 0)
mod₀-modulus-1 {𝟎}    = [≡]-intro
mod₀-modulus-1 {𝐒(a)} = [≡]-intro
  -- (𝐒(a) mod₀ 𝐒(𝟎))
  -- = [ 𝟎 , 𝟎 ] 𝐒(a) mod' 𝟎
  -- = [ 𝟎 , 𝟎 ] a mod' 𝟎

mod₀-of-modulus-pre : ∀{b} → ((b mod₀ 𝐒(b)) ≡ b)
mod₀-of-modulus-pre {𝟎}    = [≡]-intro
mod₀-of-modulus-pre {𝐒(b)} = [≡]-intro

mod₀-of-modulus-plus : ∀{a b} → ((a mod₀ (𝐒(b) + a)) ≡ a)
mod₀-of-modulus-plus {𝟎}   {_}    = [≡]-intro
mod₀-of-modulus-plus {𝐒(a)}{_}    = [≡]-intro

-- TODO: This is probably an equivalence
mod₀-loop : ∀{a b} → (a < b) → (a mod₀ b ≡ a)
mod₀-loop {a}{𝟎}    ()
mod₀-loop {a}{𝐒(b)} ([≤]-with-[𝐒] ⦃ ab ⦄) =
  [≡]-with(expr ↦ a mod₀ 𝐒(expr)) (symmetry monus-elim)
  🝖 mod₀-of-modulus-plus {a}{b −₀ a}
  where
    monus-elim : (b −₀ a) + a ≡ b
    monus-elim =
      [+]-commutativity {b −₀ a}{a}
      🝖 ([↔]-elimᵣ ([−₀][+]-nullify2 {a}{b}) ab)
  -- a < 𝐒(b)
  -- 𝐒(a) ≤ 𝐒(b)
  -- a ≤ b
  -- a + (b −₀ a) ≡ b
  -- (b −₀ a) + a ≡ b
  --
  -- a mod₀ (𝐒(b −₀ a) + a) ≡ a
  -- a mod₀ 𝐒((b −₀ a) + a) ≡ a
  -- a mod₀ 𝐒(b) ≡ a

-- TODO: Incorrect thinking in proof. ∃b∃c. (𝐒(c) + (b −₀ 𝐒(c))) ≠ b
-- mod₀-of-monus-modulus : ∀{b c} → ((b −₀ 𝐒(c)) mod₀ b ≡ b −₀ 𝐒(c))
-- mod₀-of-monus-modulus {b}{c} =
--   [≡]-with((b −₀ 𝐒(c)) mod₀_) ([−₀]ₗ[+]ₗ-nullify {𝐒(c)}{b})
--   🝖 mod₀-of-modulus-plus {b −₀ 𝐒(c)}{c}

-- mod₀-of-monus-modulus-pre : ∀{b c} → ((b −₀ c) mod₀ 𝐒(b) ≡ b −₀ c)
-- mod₀-of-monus-modulus-pre {b}   {𝟎}    = [≡]-intro
-- mod₀-of-monus-modulus-pre {𝟎}   {𝐒(c)} = [≡]-intro
-- mod₀-of-monus-modulus-pre {𝐒(b)}{𝐒(c)} = mod₀-of-monus-modulus-pre {b}{c}

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
... | [∨]-introᵣ ab0 = [≡]-with(_mod₀ b) ab0
... | [∨]-introₗ baba =
  (symmetry(mod₀-period {a −₀ b}{b})    :of: (a −₀ b mod₀ b ≡ (b + (a −₀ b)) mod₀ b))
  🝖 ([≡]-with(_mod₀ b) baba             :of: (_ ≡ a mod₀ b))
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
  🝖 [≡]-with(𝐒) proof
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
