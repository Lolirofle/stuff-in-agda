module Numeral.Finite.Bound.Proofs where

open import Data
open import Data.Boolean.Stmt
open import Functional
import      Lvl
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Finite.Proofs
import      Numeral.Finite.Oper.Comparisons as 𝕟
import      Numeral.Finite.Relation.Order as 𝕟
open import Numeral.Natural
import      Numeral.Natural.Oper.Comparisons as ℕ
open import Numeral.Natural.Oper.Comparisons.Proofs
import      Numeral.Natural.Relation as ℕ
import      Numeral.Natural.Relation.Order as ℕ
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Function.Domain
import      Structure.Function.Names as Names

private variable A B M N A₁ A₂ B₁ B₂ : ℕ
private variable n n₁ n₂ : 𝕟(N)

instance
  bound-[≤?]-injective : .⦃ ord : IsTrue(A ℕ.≤? B) ⦄ → Injective(bound-[≤?] {A}{B})
  bound-[≤?]-injective = intro proof where
    proof : .⦃ ord : IsTrue(A ℕ.≤? B) ⦄ → Names.Injective(bound-[≤?] {A}{B})
    proof{𝐒 _}{𝐒 _}{𝟎}  {𝟎}   = const [≡]-intro
    proof{𝐒 _}{𝐒 _}{𝐒 x}{𝐒 y} = congruence₁(𝐒) ∘ proof{x = x}{y} ∘ injective(𝐒)

bound-[≤?]-identity : .⦃ ord : IsTrue(A ℕ.≤? B) ⦄ → (bound-[≤?] {A}{B} n 𝕟.≡ n)
bound-[≤?]-identity {𝐒 A} {𝐒 B} {𝟎}   = <>
bound-[≤?]-identity {𝐒 A} {𝐒 B} {𝐒 n} = bound-[≤?]-identity {A}{B}{n}

bound-[≤?]-function : .⦃ ord₁ : IsTrue(A₁ ℕ.≤? B₁) ⦄ → .⦃ ord₂ : IsTrue(A₂ ℕ.≤? B₂) ⦄ → (n₁ 𝕟.≡ n₂) → (bound-[≤?] {A₁}{B₁} n₁ 𝕟.≡ bound-[≤?] {A₂}{B₂} n₂)
bound-[≤?]-function {𝐒 A₁}{𝐒 B₁}{𝐒 A₂}{𝐒 B₂} {𝟎}   {𝟎}    en = <>
bound-[≤?]-function {𝐒 A₁}{𝐒 B₁}{𝐒 A₂}{𝐒 B₂} {𝐒 n₁}{𝐒 n₂} en = bound-[≤?]-function {A₁}{B₁}{A₂}{B₂} {n₁}{n₂} en

bound-[≤?]-id : bound-[≤?] {N}{N} ⦃ [≤?]-reflexivity {N} ⦄ n ≡ n
bound-[≤?]-id {n = 𝟎}   = [≡]-intro
bound-[≤?]-id {n = 𝐒 n} = congruence₁(𝐒) (bound-[≤?]-id {n = n})

bound-𝐒-identity : bound-𝐒(n) 𝕟.≡ n
bound-𝐒-identity{N}{n} = bound-[≤?]-identity {n = n} ⦃ [≤?]-𝐒 {N} ⦄

bound-𝐒-function : (n₁ 𝕟.≡ n₂) → (bound-𝐒(n₁) 𝕟.≡ bound-𝐒(n₂))
bound-𝐒-function{N₁}{n₁}{N₂}{n₂} = bound-[≤?]-function {n₁ = n₁}{n₂ = n₂} ⦃ [≤?]-𝐒 {N₁} ⦄ ⦃ [≤?]-𝐒 {N₂} ⦄

bound-𝐒-injective : (bound-𝐒(n₁) 𝕟.≡ bound-𝐒(n₂)) → (n₁ 𝕟.≡ n₂)
bound-𝐒-injective {n₁ = 𝟎}    {n₂ = 𝟎}    p = <>
bound-𝐒-injective {n₁ = 𝐒 n₁} {n₂ = 𝐒 n₂} p = bound-𝐒-injective {n₁ = n₁} {n₂ = n₂} p

bound-𝐒-not-maximum : bound-𝐒(n) ≢ maximum
bound-𝐒-not-maximum {.(𝐒 _)} {𝟎} ()
bound-𝐒-not-maximum {.(𝐒 _)} {𝐒 n} eq = bound-𝐒-not-maximum {n = n} (injective(𝐒) eq)

bound-𝐒-is-maximum-condition : ⦃ pos : ℕ.Positive(M) ⦄ → (bound-𝐒(n) 𝕟.≡ maximum{M}) → (M ℕ.≤ bound(n))
bound-𝐒-is-maximum-condition {𝐒 𝟎}     {𝐒 N}     {𝟎}   eq = ℕ.succ ℕ.min
bound-𝐒-is-maximum-condition {𝐒 (𝐒 M)} {𝐒 (𝐒 N)} {𝐒 n} eq = ℕ.succ(bound-𝐒-is-maximum-condition {𝐒 M} {𝐒 N} {n} eq)

[⋚?]-of-bound-[≤?] : .⦃ ord₁ : IsTrue(A₁ ℕ.≤? B₁) ⦄ → .⦃ ord₂ : IsTrue(A₂ ℕ.≤? B₂) ⦄ → ((bound-[≤?] {A₁}{B₁} n₁ 𝕟.⋚? bound-[≤?] {A₂}{B₂} n₂) ≡ (n₁ 𝕟.⋚? n₂))
[⋚?]-of-bound-[≤?] {𝐒 A₁}{𝐒 B₁}{𝐒 A₂}{𝐒 B₂} {n₁ = 𝟎}   {n₂ = 𝟎}    = [≡]-intro
[⋚?]-of-bound-[≤?] {𝐒 A₁}{𝐒 B₁}{𝐒 A₂}{𝐒 B₂} {n₁ = 𝟎}   {n₂ = 𝐒 n₂} = [≡]-intro
[⋚?]-of-bound-[≤?] {𝐒 A₁}{𝐒 B₁}{𝐒 A₂}{𝐒 B₂} {n₁ = 𝐒 n₁}{n₂ = 𝟎}    = [≡]-intro
[⋚?]-of-bound-[≤?] {𝐒 A₁}{𝐒 B₁}{𝐒 A₂}{𝐒 B₂} {n₁ = 𝐒 n₁}{n₂ = 𝐒 n₂} = [⋚?]-of-bound-[≤?] {A₁}{B₁}{A₂}{B₂} {n₁ = n₁}{n₂ = n₂}

[⋚?]-of-bound-𝐒 : (bound-𝐒 n₁ 𝕟.⋚? bound-𝐒 n₂) ≡ (n₁ 𝕟.⋚? n₂)
[⋚?]-of-bound-𝐒 {N₁} {n₁} {N₂} {n₂} = [⋚?]-of-bound-[≤?] {n₁ =  n₁}{n₂ = n₂} ⦃ [≤?]-𝐒 {n = N₁} ⦄ ⦃ [≤?]-𝐒 {n = N₂} ⦄
