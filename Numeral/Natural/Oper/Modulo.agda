module Numeral.Natural.Oper.Modulo where

import Lvl
open import Data.Boolean.AsSet
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper
open import Numeral.Natural.UnclosedOper

infixl 10100 _mod_

-- Modulo is defined using this.
-- This, unlike (_mod_) is keeping internal state of the previous value.
-- `r` is the current result. Should be 0 at the start.
-- `b` is the modulus. This value will not change in the repeated applications of the function.
-- `a'` is the number to take the modulo of.
-- 'b'` is the temporary modulus. Should be `b` at the start.
-- This function works by repeatedly decreasing `a'` and `b'` and at the same time increasing `r` until `b'` is 0.
-- When `b'` is 0, `r` is resetted to 0, and `b'` is resetted to `b`.
-- Almost the same algorithm imperatively:
--   while a'!=0{
--     a'-= 1;
--     b'-= 1;
--     r += 1;
--     if b'==0{
--       r := 0;
--       b':= b;
--     }
--   }
--   return r;
-- Example execution:
--   [ 0 , 2 ] 5 mod' 2
--   = [ 1 , 2 ] 4 mod' 1
--   = [ 2 , 2 ] 3 mod' 0
--   = [ 0 , 2 ] 3 mod' 2
--   = [ 1 , 2 ] 2 mod' 1
--   = [ 2 , 2 ] 1 mod' 0
--   = [ 0 , 2 ] 1 mod' 2
--   = [ 1 , 2 ] 0 mod' 1
--   = 1
-- The above is describing the following code:
--   {-# TERMINATING #-}
--   [_,_]_mod₀'_ : ℕ → ℕ → ℕ → ℕ → ℕ
--   [ _ , 𝟎 ] _     mod₀' _     = 𝟎
--   [ _ , b ] a'    mod₀' 𝟎     = [ 𝟎    , b ] a' mod₀' b
--   [ r , _ ] 𝟎     mod₀' _     = r
--   [ r , b ] 𝐒(a') mod₀' 𝐒(b') = [ 𝐒(r) , b ] a' mod₀' b'
-- Then it is transformed to the following code (So that it terminates):
--   [_,_]_mod₀'_ : ℕ → ℕ → ℕ → ℕ → ℕ
--   [ _ , 𝟎    ] _     mod₀' _     = 𝟎
--   [ _ , 𝐒(_) ] 𝟎     mod₀' 𝟎     = 𝟎
--   [ r , 𝐒(_) ] 𝟎     mod₀' 𝐒(_)  = r
--   [ _ , 𝐒(b) ] 𝐒(a') mod₀' 𝟎     = [ 𝐒(𝟎) , 𝐒(b) ] a' mod₀' b
--   [ r , 𝐒(b) ] 𝐒(a') mod₀' 𝐒(b') = [ 𝐒(r) , 𝐒(b) ] a' mod₀' b'
-- And finally removing the forbidden 𝟎 cases of `b` and `b'` by just interpreting (b=0), (b'=0) in this function as 1's:
--   [ r , _ ] 𝟎     mod' _     = r
--   [ _ , b ] 𝐒(a') mod' 𝟎     = [ 𝟎 , b ] a' mod' b
--   [ r , b ] 𝐒(a') mod' 𝐒(b') = [ 𝐒(r) , b ] a' mod' b'
[_,_]_mod'_ : ℕ → ℕ → ℕ → ℕ → ℕ
[ r , _ ] 𝟎     mod' _     = r
[ _ , b ] 𝐒(a') mod' 𝟎     = [ 𝟎    , b ] a' mod' b
[ r , b ] 𝐒(a') mod' 𝐒(b') = [ 𝐒(r) , b ] a' mod' b'
{-# BUILTIN NATMODSUCAUX [_,_]_mod'_ #-}

-- Difference between the value before and after the floored division operation.
_mod_ : ℕ → (m : ℕ) → ∀{ℓ} → ⦃ _ : BoolIsTrue{ℓ}(m ≢? 𝟎)⦄ → ℕ
_mod_ a 𝟎 ⦃ ⦄
_mod_ a (𝐒(b)) = [ 0 , b ] a mod' b

_mod₀_ : ℕ → ℕ → ℕ
_mod₀_ a 𝟎      = 0
_mod₀_ a (𝐒(b)) = [ 0 , b ] a mod' b
