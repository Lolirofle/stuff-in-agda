module Numeral.Natural.Oper.Comparisons.Proofs where

open import Data.Boolean.Stmt
open import Data.Boolean
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Relator.Equals


[≤?]-𝟎 : ∀{n} → IsTrue(𝟎 ≤? n)
[≤?]-𝟎 = [⊤]-intro

[≤?]-𝐒 : ∀{n} → IsTrue(n ≤? 𝐒(n))
[≤?]-𝐒 {𝟎}   = [⊤]-intro
[≤?]-𝐒 {𝐒 n} = [≤?]-𝐒 {n}

[<?]-𝟎 : ∀{n} → IsTrue(𝟎 <? 𝐒(n))
[<?]-𝟎 {𝟎}   = [⊤]-intro
[<?]-𝟎 {𝐒 n} = [<?]-𝟎 {n}

[<?]-𝐒 : ∀{n} → IsTrue(n <? 𝐒(n))
[<?]-𝐒 {𝟎}   = [⊤]-intro
[<?]-𝐒 {𝐒 n} = [<?]-𝐒 {n}

[≤?]-reflexivity : ∀{n} → IsTrue(n ≤? n)
[≤?]-reflexivity {𝟎}    = [⊤]-intro
[≤?]-reflexivity {𝐒(n)} = [≤?]-reflexivity {n}

[<?]-positive : ∀{n} → (𝟎 <? n) ≡ positive?(n)
[<?]-positive {𝟎}    = [≡]-intro
[<?]-positive {𝐒(_)} = [≡]-intro
{-# REWRITE [<?]-positive #-}

[<?]-positive-any : ∀{m n} → ⦃ _ : IsTrue(m <? n) ⦄ → IsTrue(positive?(n))
[<?]-positive-any {𝟎}   {n}   ⦃ p ⦄ = p
[<?]-positive-any {𝐒 m} {𝐒 n} ⦃ p ⦄ = [⊤]-intro

[≤?]-positive : ∀{n} → (𝐒(𝟎) ≤? n) ≡ positive?(n)
[≤?]-positive {𝟎}    = [≡]-intro
[≤?]-positive {𝐒(_)} = [≡]-intro

[≢?]-positive : ∀{n} → (n ≢? 𝟎) ≡ positive?(n)
[≢?]-positive {𝟎}    = [≡]-intro
[≢?]-positive {𝐒(_)} = [≡]-intro

[<?]-to-[≤?] : ∀{a b} → ((a <? b) ≡ (𝐒(a) ≤? b))
[<?]-to-[≤?] {𝟎}   {𝟎}    = [≡]-intro
[<?]-to-[≤?] {𝟎}   {𝐒(_)} = [≡]-intro
[<?]-to-[≤?] {𝐒(_)}{𝟎}    = [≡]-intro
[<?]-to-[≤?] {𝐒(a)}{𝐒(b)} = [<?]-to-[≤?] {a}{b}
