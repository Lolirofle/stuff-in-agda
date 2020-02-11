module Numeral.Natural.Oper.FlooredDivision where

import Lvl
open import Data
open import Data.Boolean.Stmt
open import Logic.Propositional.Theorems
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Relator.Equals

infixl 10100 _⌊/⌋_

-- Inductive definition of an algorithm for division.
-- `[ d , b ] a' div b'` should be interpreted as following:
--   `d` is the result of the algorithm that is being incremented as it runs.
--   `b` is the predecessor of the original denominator. This is constant throughout the whole process.
--   `a'` is the numerator. This is decremented as it runs.
--   `b'` is the predecessor of the temporary denominator. This is decremented as it runs.
-- By decrementing both `a'` and `b'`, and incrementing `d` when 'b`' reaches 0, it counts how many times `b` "fits into" `a`. 
-- Note: See Numeral.Natural.Oper.Modulo for a similiar algorithm used to determine the modulo.
[_,_]_div_ : ℕ → ℕ → ℕ → ℕ → ℕ
[ d , _ ] 𝟎     div _     = d
[ d , b ] 𝐒(a') div 𝟎     = [ 𝐒(d) , b ] a' div b
[ d , b ] 𝐒(a') div 𝐒(b') = [ d   , b ] a' div b'
{-# BUILTIN NATDIVSUCAUX [_,_]_div_ #-}

-- Floored division operation.
_⌊/⌋_ : ℕ → (m : ℕ) → ⦃ _ : IsTrue(m ≢? 𝟎)⦄ → ℕ
a ⌊/⌋ 𝐒(m) = [ 𝟎 , m ] a div m

_⌊/⌋₀_ : ℕ → ℕ → ℕ
_ ⌊/⌋₀ 𝟎    = 𝟎
a ⌊/⌋₀ 𝐒(m) = a ⌊/⌋ 𝐒(m)
{-# INLINE _⌊/⌋₀_ #-}




-- TODO: Move below to a separate proofs document
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Relator.Equals.Proofs

private variable d d₁ d₂ b a' b' : ℕ

inddiv-result-𝐒 : [ 𝐒 d , b ] a' div b' ≡ 𝐒([ d , b ] a' div b')
inddiv-result-𝐒 {d} {b} {𝟎}    {b'}   = [≡]-intro
inddiv-result-𝐒 {d} {b} {𝐒 a'} {𝟎}    = inddiv-result-𝐒 {𝐒 d} {b} {a'} {b}
inddiv-result-𝐒 {d} {b} {𝐒 a'} {𝐒 b'} = inddiv-result-𝐒 {d}{b}{a'}{b'}
{-# REWRITE inddiv-result-𝐒 #-}

inddiv-result : [ d , b ] a' div b' ≡ d + ([ 𝟎 , b ] a' div b')
inddiv-result {𝟎}              = [≡]-intro
inddiv-result {𝐒 d}{b}{a'}{b'} = [≡]-with(𝐒) (inddiv-result {d}{b}{a'}{b'})

inddiv-of-denominator : [ d , b ] b' div b' ≡ d
inddiv-of-denominator {d} {b} {𝟎}    = [≡]-intro
inddiv-of-denominator {d} {b} {𝐒 b'} = inddiv-of-denominator{d}{b}{b'}

inddiv-of-denominator-successor : [ d , b ] 𝐒 b' div b' ≡ 𝐒 d
inddiv-of-denominator-successor {d} {b} {𝟎}    = [≡]-intro
inddiv-of-denominator-successor {d} {b} {𝐒 b'} = inddiv-of-denominator-successor{d}{b}{b'}

inddiv-step-denominator : [ d , b ] (a' + b') div b' ≡ [ d , b ] a' div 𝟎
inddiv-step-denominator {_} {_} {_}  {𝟎}    = [≡]-intro
inddiv-step-denominator {d} {b} {a'} {𝐒 b'} = inddiv-step-denominator {d} {b} {a'} {b'}



[⌊/⌋]-of-0ₗ : ∀{n} → ⦃ _ : IsTrue(n ≢? 𝟎)⦄ → (𝟎 ⌊/⌋ n ≡ 𝟎)
[⌊/⌋]-of-0ₗ {𝐒 n} = [≡]-intro

[⌊/⌋]-of-1ₗ : ∀{n} → ⦃ _ : IsTrue(n ≢? 𝟎)⦄ → ⦃ _ : IsTrue(n ≢? 1)⦄ → (1 ⌊/⌋ n ≡ 𝟎)
[⌊/⌋]-of-1ₗ {𝐒 (𝐒 n)} = [≡]-intro

[⌊/⌋]-of-1ᵣ : ∀{m} → (m ⌊/⌋ 1 ≡ m)
[⌊/⌋]-of-1ᵣ {𝟎} = [≡]-intro
[⌊/⌋]-of-1ᵣ {𝐒 m} = [≡]-with(𝐒) ([⌊/⌋]-of-1ᵣ {m})

[⌊/⌋]-of-same : ∀{n} → ⦃ _ : IsTrue(n ≢? 𝟎)⦄ → (n ⌊/⌋ n ≡ 1)
[⌊/⌋]-of-same {𝐒 n} = inddiv-of-denominator-successor {b' = n}

{-
[⌊/⌋]-of-[+]ₗ : ∀{m n} → ⦃ _ : IsTrue(n ≢? 𝟎)⦄ → ((m + n) ⌊/⌋ n ≡ 𝐒(m ⌊/⌋ n))
[⌊/⌋]-of-[+]ₗ {_}   {𝐒 𝟎}     = [≡]-intro
[⌊/⌋]-of-[+]ₗ {𝟎}   {𝐒 (𝐒 n)} = [≡]-intro
[⌊/⌋]-of-[+]ₗ {𝐒 m} {𝐒 (𝐒 n)} = {![⌊/⌋]-of-[+]ₗ {m} {𝐒 (𝐒 n)}!}

[⌊/⌋]-is-0 : ∀{m n} → ⦃ _ : IsTrue(n ≢? 𝟎)⦄ → (m ⌊/⌋ n ≡ 𝟎) → (m ≡ 𝟎)
[⌊/⌋]-is-0 {𝟎}   {𝐒 n}    _ = [≡]-intro
[⌊/⌋]-is-0 {𝐒 m} {𝐒(𝐒 n)} p with [⌊/⌋]-is-0 {𝐒 m} {𝐒 n} {!!}
... | pp = {!!}
-}
