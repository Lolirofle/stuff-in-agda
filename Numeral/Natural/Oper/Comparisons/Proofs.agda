module Numeral.Natural.Oper.Comparisons.Proofs where

open import Data.Boolean.Stmt
open import Data.Boolean
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Proofs
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

[≡?]-zero : ∀{n} → (n ≡? 𝟎) ≡ zero?(n)
[≡?]-zero {𝟎}    = [≡]-intro
[≡?]-zero {𝐒(_)} = [≡]-intro

[≤?]-transitivity : ∀{x y z} → IsTrue(x ≤? y) → IsTrue(y ≤? z) → IsTrue(x ≤? z)
[≤?]-transitivity {𝟎}                xy yz = [⊤]-intro
[≤?]-transitivity {𝐒 x}   {𝟎}  {𝟎}   xy yz = xy
[≤?]-transitivity {𝐒 𝟎}   {𝟎}  {𝐒 z} xy yz = [⊤]-intro
[≤?]-transitivity {𝐒(𝐒 x)}{𝟎}  {𝐒 z} xy yz = [≤?]-transitivity {𝐒 x}{𝟎}{z} xy [⊤]-intro
[≤?]-transitivity {𝐒 x}   {𝐒 y}{𝟎}   xy yz = yz
[≤?]-transitivity {𝐒 x}   {𝐒 y}{𝐒 z} xy yz = [≤?]-transitivity {x}{y}{z} xy yz

[<?][≤?]-subtransitivityᵣ : ∀{x y z} → IsTrue(x <? y) → IsTrue(y ≤? z) → IsTrue(x <? z)
[<?][≤?]-subtransitivityᵣ {_}  {𝟎}  {𝟎}   xy yz = xy
[<?][≤?]-subtransitivityᵣ {_}  {𝐒 y}{𝟎}   xy yz = yz
[<?][≤?]-subtransitivityᵣ {𝟎}  {𝟎}  {𝐒 _} xy yz = [⊤]-intro
[<?][≤?]-subtransitivityᵣ {𝟎}  {𝐒 _}{𝐒 _} xy yz = [⊤]-intro
[<?][≤?]-subtransitivityᵣ {𝐒 x}{𝟎}  {𝐒 z} xy yz = [<?][≤?]-subtransitivityᵣ {x}{𝟎}{z} xy [⊤]-intro
[<?][≤?]-subtransitivityᵣ {𝐒 x}{𝐒 y}{𝐒 z} xy yz = [<?][≤?]-subtransitivityᵣ {x}{y}{z} xy yz

{-
[≤?][⋚?]-def : ∀{x y} → ((x ≤? y) ≡ (elim₃ 𝑇 𝑇 𝐹 (x ⋚? y)))
[≤?][⋚?]-def {𝟎}  {𝟎}   = [≡]-intro
[≤?][⋚?]-def {𝟎}  {𝐒 y} = [≡]-intro
[≤?][⋚?]-def {𝐒 x}{𝟎}   = [≡]-intro
[≤?][⋚?]-def {𝐒 x}{𝐒 y} = [≤?][⋚?]-def {x}{y}
-}
