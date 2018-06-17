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

-- [mod₀']-1 : ∀{b b'} → ([ 𝟎 , b ] 𝟎 mod₀' b' ≡ 𝟎)
-- [mod₀']-1 {𝟎}   {𝟎}    = [≡]-intro
-- [mod₀']-1 {𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀']-1 {𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀']-1 {𝐒(_)}{𝐒(_)} = [≡]-intro
-- {-# REWRITE [mod₀']-1 #-}

-- [mod₀']-2 : ∀{r b b'} → [ r , 𝐒(b) ] 𝟎 mod₀' 𝐒(b') ≡ r
-- [mod₀']-2 = [≡]-intro

-- [mod₀']-3 : ∀{r a' b'} → [ r , 𝟎 ] a' mod₀' b' ≡ 𝟎
-- [mod₀']-3 = [≡]-intro

-- [mod₀']-4 : ∀{r b} → [ r , b ] 𝟎 mod₀' 𝟎 ≡ 𝟎
-- [mod₀']-4 {_}{𝟎}    = [≡]-intro
-- [mod₀']-4 {_}{𝐒(_)} = [≡]-intro
-- {-# REWRITE [mod₀']-4 #-}

-- [mod₀']-5 : ∀{r b a' b'} → [ r , b ] 𝐒(a') mod₀' 𝐒(b') ≡ [ 𝐒(r) , b ] a' mod₀' b'
-- [mod₀']-5 {𝟎}   {𝟎}   {𝟎}   {𝟎}    = [≡]-intro
-- [mod₀']-5 {𝟎}   {𝟎}   {𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀']-5 {𝟎}   {𝟎}   {𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀']-5 {𝟎}   {𝟎}   {𝐒(_)}{𝐒(_)} = [≡]-intro
-- [mod₀']-5 {𝟎}   {𝐒(_)}{𝟎}   {𝟎}    = [≡]-intro
-- [mod₀']-5 {𝟎}   {𝐒(_)}{𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀']-5 {𝟎}   {𝐒(_)}{𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀']-5 {𝟎}   {𝐒(_)}{𝐒(_)}{𝐒(_)} = [≡]-intro
-- [mod₀']-5 {𝐒(_)}{𝟎}   {𝟎}   {𝟎}    = [≡]-intro
-- [mod₀']-5 {𝐒(_)}{𝟎}   {𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀']-5 {𝐒(_)}{𝟎}   {𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀']-5 {𝐒(_)}{𝟎}   {𝐒(_)}{𝐒(_)} = [≡]-intro
-- [mod₀']-5 {𝐒(_)}{𝐒(_)}{𝟎}   {𝟎}    = [≡]-intro
-- [mod₀']-5 {𝐒(_)}{𝐒(_)}{𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀']-5 {𝐒(_)}{𝐒(_)}{𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀']-5 {𝐒(_)}{𝐒(_)}{𝐒(_)}{𝐒(_)} = [≡]-intro
-- {-# REWRITE [mod₀']-5 #-}

-- [mod₀']-6 : ∀{r b a'} → [ r , b ] a' mod₀' 𝟎 ≡ [ 𝟎 , b ] a' mod₀' b
-- [mod₀']-6 {𝟎}   {𝟎}   {𝟎}    = [≡]-intro
-- [mod₀']-6 {𝟎}   {𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀']-6 {𝟎}   {𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀']-6 {𝟎}   {𝐒(_)}{𝐒(_)} = [≡]-intro
-- [mod₀']-6 {𝐒(_)}{𝟎}   {𝟎}    = [≡]-intro
-- [mod₀']-6 {𝐒(_)}{𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀']-6 {𝐒(_)}{𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀']-6 {𝐒(_)}{𝐒(_)}{𝐒(_)} = [≡]-intro
-- {-# REWRITE [mod₀']-6 #-}

-- [mod₀']-7 : ∀{r b y} → [ r , b ] y mod₀' y ≡ 𝟎
-- [mod₀']-7 {𝟎}   {𝟎}   {𝟎}    = [≡]-intro
-- [mod₀']-7 {𝟎}   {𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀']-7 {𝟎}   {𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀']-7 {𝐒(_)}{𝟎}   {𝟎}    = [≡]-intro
-- [mod₀']-7 {𝐒(_)}{𝟎}   {𝐒(_)} = [≡]-intro
-- [mod₀']-7 {𝐒(_)}{𝐒(_)}{𝟎}    = [≡]-intro
-- [mod₀']-7 {r}   {𝐒(b)}{𝐒(y)} = [mod₀']-7 {𝐒(r)}{𝐒(b)}{y}
-- {-# REWRITE [mod₀']-7 #-}

-- modulo-of-0 : ∀{b} → ((0 mod₀ b) ≡ 0)
-- modulo-of-0 = [≡]-intro

-- modulo-of-modulus : ∀{b} → ((b mod₀ b) ≡ 0)
-- modulo-of-modulus = [≡]-intro

-- modulo-period : ∀{a b} → (((a + b) mod₀ b) ≡ (a mod₀ b))
-- modulo-period {𝟎}   {b}    = [≡]-intro
-- modulo-period {𝐒(a)}{b}    = modulo-period {a}{b}

{-
((𝐒(a) + 𝐒(b)) mod₀ 𝐒(b))
(𝐒(𝐒(a) + b) mod₀ 𝐒(b))
((𝐒(a) + b) mod₀ b)

(𝐒(a) mod₀ 𝐒(b))
(a mod₀ b)
-}

-- postulate modulo-of-right-multiple : ∀{a b} → (((a ⋅ b) mod₀ b) ≡ 0)

-- postulate modulo-lower-bound : ∀{a b} → (0 ≤ (a mod₀ b))

-- postulate modulo-upper-bound : ∀{a b} → ⦃ proof : (b ≢ 0) ⦄ → ((a mod b) ⦃ proof ⦄ < b)

-- postulate modulo-identity : ∀{a b} → (a < b) → ((a mod₀ b) ≡ a)

-- postulate modulo-nested : ∀{a b} → (((a mod₀ b) mod₀ b) ≡ (a mod₀ b))

-- postulate modulo-successor : ∀{a b} → ((𝐒(a) mod₀ b) ≡ (𝐒(a mod₀ b) mod₀ b))

-- postulate modulo-addition : ∀{a₁ a₂ b} → (((a₁ + a₂) mod₀ b) ≡ (((a₁ mod₀ b) + (a₂ mod₀ b)) mod₀ b))

-- postulate modulo-multiplication : ∀{a₁ a₂ b} → (((a₁ ⋅ a₂) mod₀ b) ≡ (((a₁ mod₀ b) ⋅ (a₂ mod₀ b)) mod₀ b))

-- postulate modulo-thing : a −₀ ((a ⌊/₀⌋ b) ⋅ b) ≡ a mod b
module One where
  test0 : (0 mod 1) ≡ 0
  test0 = [≡]-intro

  test1 : (1 mod 1) ≡ 0
  test1 = [≡]-intro

  test2 : (2 mod 1) ≡ 0
  test2 = [≡]-intro

  test3 : (3 mod 1) ≡ 0
  test3 = [≡]-intro

  test4 : (4 mod 1) ≡ 0
  test4 = [≡]-intro

  test5 : (5 mod 1) ≡ 0
  test5 = [≡]-intro

  test6 : (6 mod 1) ≡ 0
  test6 = [≡]-intro

  test7 : (7 mod 1) ≡ 0
  test7 = [≡]-intro

  test8 : (8 mod 1) ≡ 0
  test8 = [≡]-intro

  test9 : (9 mod 1) ≡ 0
  test9 = [≡]-intro

  test10 : (10 mod 1) ≡ 0
  test10 = [≡]-intro

  test11 : (11 mod 1) ≡ 0
  test11 = [≡]-intro
