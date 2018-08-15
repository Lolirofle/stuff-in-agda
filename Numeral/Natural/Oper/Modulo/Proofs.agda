module Numeral.Natural.Oper.Modulo.Proofs{ℓ} where

import Lvl
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Relation{ℓ}
open import Numeral.Natural.UnclosedOper
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Proofs{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- mod'

[mod₀]-1 : ∀{b b'} → ([ 𝟎 , b ] 𝟎 mod' b' ≡ 𝟎)
[mod₀]-1 {𝟎}   {𝟎}    = [≡]-intro
[mod₀]-1 {𝐒(_)}{𝟎}    = [≡]-intro
[mod₀]-1 {𝟎}   {𝐒(_)} = [≡]-intro
[mod₀]-1 {𝐒(_)}{𝐒(_)} = [≡]-intro

[mod₀]-2 : ∀{r b b'} → [ r , 𝐒(b) ] 𝟎 mod' 𝐒(b') ≡ r
[mod₀]-2 = [≡]-intro

-- [mod₀]-3 : ∀{r a' b'} → [ r , 𝟎 ] a' mod₀ b' ≡ 𝟎
-- [mod₀]-3 = [≡]-intro

-- [mod₀]-4 : ∀{r b} → [ r , b ] 𝟎 mod₀ 𝟎 ≡ 𝟎
-- [mod₀]-4 {_}{𝟎}    = [≡]-intro
-- [mod₀]-4 {_}{𝐒(_)} = [≡]-intro
-- {-# REWRITE [mod₀]-4 #-}

[mod₀]-5 : ∀{r b a' b'} → [ r , b ] 𝐒(a') mod' 𝐒(b') ≡ [ 𝐒(r) , b ] a' mod' b'
[mod₀]-5 {𝟎}   {𝟎}   {𝟎}   {𝟎}    = [≡]-intro
[mod₀]-5 {𝟎}   {𝟎}   {𝟎}   {𝐒(_)} = [≡]-intro
[mod₀]-5 {𝟎}   {𝟎}   {𝐒(_)}{𝟎}    = [≡]-intro
[mod₀]-5 {𝟎}   {𝟎}   {𝐒(_)}{𝐒(_)} = [≡]-intro
[mod₀]-5 {𝟎}   {𝐒(_)}{𝟎}   {𝟎}    = [≡]-intro
[mod₀]-5 {𝟎}   {𝐒(_)}{𝟎}   {𝐒(_)} = [≡]-intro
[mod₀]-5 {𝟎}   {𝐒(_)}{𝐒(_)}{𝟎}    = [≡]-intro
[mod₀]-5 {𝟎}   {𝐒(_)}{𝐒(_)}{𝐒(_)} = [≡]-intro
[mod₀]-5 {𝐒(_)}{𝟎}   {𝟎}   {𝟎}    = [≡]-intro
[mod₀]-5 {𝐒(_)}{𝟎}   {𝟎}   {𝐒(_)} = [≡]-intro
[mod₀]-5 {𝐒(_)}{𝟎}   {𝐒(_)}{𝟎}    = [≡]-intro
[mod₀]-5 {𝐒(_)}{𝟎}   {𝐒(_)}{𝐒(_)} = [≡]-intro
[mod₀]-5 {𝐒(_)}{𝐒(_)}{𝟎}   {𝟎}    = [≡]-intro
[mod₀]-5 {𝐒(_)}{𝐒(_)}{𝟎}   {𝐒(_)} = [≡]-intro
[mod₀]-5 {𝐒(_)}{𝐒(_)}{𝐒(_)}{𝟎}    = [≡]-intro
[mod₀]-5 {𝐒(_)}{𝐒(_)}{𝐒(_)}{𝐒(_)} = [≡]-intro
-- {-# REWRITE [mod₀]-5 #-}

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
{-# REWRITE mod'-of-modulus-part #-}
  -- [ r , 0 ] 𝐒(𝐒(b')) mod' 𝐒(b')
  -- = [ r + 1 , 0 ] 𝐒(b') mod' b'
  -- = ...
  -- = [ r + 𝐒(b') , 0 ] 1 mod' 0

mod'-of-modulus : ∀{b} → [ 0 , b ] 𝐒(b) mod' b ≡ [ 0 , b ] 0 mod' b
mod'-of-modulus{𝟎}       = [≡]-intro
mod'-of-modulus{𝐒(𝟎)}    = [≡]-intro
mod'-of-modulus{𝐒(𝐒(b))} = [≡]-intro -- mod'-of-modulus-part{𝐒(𝐒(b))}{𝐒(𝐒(b))}{0} where
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

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- mod₀

mod₀-of-0 : ∀{b} → ((0 mod₀ b) ≡ 0)
mod₀-of-0 {𝟎}    = [≡]-intro
mod₀-of-0 {𝐒(b)} = [≡]-intro

mod₀-of-modulus : ∀{b} → ((b mod₀ b) ≡ 0)
mod₀-of-modulus {𝟎}    = [≡]-intro
mod₀-of-modulus {𝐒(b)} = [≡]-intro

-- mod₀-period : ∀{a b} → (((b + a) mod₀ b) ≡ (a mod₀ b))
-- mod₀-period {𝟎}   {𝟎}       = [≡]-intro
-- mod₀-period {𝟎}   {𝐒(b)}    = [≡]-intro
-- mod₀-period {𝐒(a)}{𝟎}       = [≡]-intro
-- mod₀-period {𝐒(a)}{𝐒(b)}    = [≡]-intro

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

-- postulate modulo-of-right-multiple : ∀{a b} → (((a ⋅ b) mod₀ b) ≡ 0)

-- postulate modulo-upper-bound : ∀{a b} → ⦃ proof : (b ≢ 0) ⦄ → ((a mod b) ⦃ proof ⦄ < b)

-- postulate modulo-identity : ∀{a b} → (a < b) → ((a mod₀ b) ≡ a)

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
