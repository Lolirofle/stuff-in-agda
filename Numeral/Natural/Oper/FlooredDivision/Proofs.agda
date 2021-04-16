module Numeral.Natural.Oper.FlooredDivision.Proofs where

import      Lvl
open import Data
open import Data.Boolean.Stmt
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Comparisons.Proofs
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
open import Relator.Equals
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

inddiv-smaller : (a' ≤ b') → ([ d , b ] a' div b' ≡ d)
inddiv-smaller min = [≡]-intro
inddiv-smaller {d = d}{b} (succ {𝟎}   {𝟎}    p) = [≡]-intro
inddiv-smaller {d = d}{b} (succ {𝟎}   {𝐒 b'} p) = [≡]-intro
inddiv-smaller {d = d}{b} (succ {𝐒 a'}{𝐒 b'} p) = inddiv-smaller {d = d}{b} p



[⌊/⌋][⌊/⌋₀]-equality : ∀{a b} → ⦃ _ : IsTrue(positive?(b))⦄ → (a ⌊/⌋₀ b ≡ a ⌊/⌋ b)
[⌊/⌋][⌊/⌋₀]-equality {b = 𝐒 b} = [≡]-intro

[⌊/⌋]-of-0ₗ : ∀{n} → ⦃ _ : IsTrue(positive?(n))⦄ → (𝟎 ⌊/⌋ n ≡ 𝟎)
[⌊/⌋]-of-0ₗ {𝐒 n} = [≡]-intro

[⌊/⌋]-of-1ₗ : ∀{n} → ⦃ _ : IsTrue(positive?(n))⦄ → ⦃ _ : IsTrue(n ≢? 1)⦄ → (1 ⌊/⌋ n ≡ 𝟎)
[⌊/⌋]-of-1ₗ {𝐒 (𝐒 n)} = [≡]-intro

[⌊/⌋]-of-1ᵣ : ∀{m} → (m ⌊/⌋ 1 ≡ m)
[⌊/⌋]-of-1ᵣ {𝟎} = [≡]-intro
[⌊/⌋]-of-1ᵣ {𝐒 m} = [≡]-with(𝐒) ([⌊/⌋]-of-1ᵣ {m})

[⌊/⌋]-of-same : ∀{n} → ⦃ _ : IsTrue(positive?(n))⦄ → (n ⌊/⌋ n ≡ 1)
[⌊/⌋]-of-same {𝐒 n} = inddiv-of-denominator-successor {b' = n}

postulate [⌊/⌋]-positive : ∀{a b} ⦃ _ : Positive(a) ⦄ ⦃ _ : Positive(b) ⦄ → Positive(a ⌊/⌋ b)

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

postulate [⌊/⌋]-leₗ : ∀{a b} ⦃ _ : IsTrue(positive?(b))⦄ → (a ⌊/⌋ b ≤ a)

postulate [⌊/⌋]-ltₗ : ∀{a} ⦃ _ : IsTrue(positive?(a))⦄ {b} ⦃ b-proof : IsTrue(b >? 1)⦄ → ((a ⌊/⌋ b) ⦃ [<?]-positive-any {1}{b} ⦄ < a)

postulate [⌊/⌋]-zero : ∀{a b} ⦃ _ : IsTrue(positive?(b))⦄ → (a < b) → (a ⌊/⌋ b ≡ 𝟎)

postulate [⌊/⌋]-preserve-[<]ₗ : ∀{a b d} ⦃ _ : IsTrue(positive?(b))⦄ ⦃ _ : IsTrue(positive?(d))⦄ → (a < b) → (a ⌊/⌋ d < b)

postulate [⌊/⌋][+]-distributivityᵣ : ∀{a b c} ⦃ _ : IsTrue(positive?(c))⦄ → ((a + b) ⌊/⌋ c ≡ (a ⌊/⌋ c) + (b ⌊/⌋ c))
