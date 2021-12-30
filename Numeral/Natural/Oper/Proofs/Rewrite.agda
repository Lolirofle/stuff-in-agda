module Numeral.Natural.Oper.Proofs.Rewrite where

import Lvl
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Induction
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Syntax.Function

private variable x y : ℕ

[+]-baseₗ : 𝟎 + y ≡ y
[+]-baseₗ {x} = ℕ-elim _ [≡]-intro (x ↦ congruence₁(𝐒) {𝟎 + x}{x}) x
{-# REWRITE [+]-baseₗ #-}

[+]-baseᵣ : x + 𝟎 ≡ x
[+]-baseᵣ = [≡]-intro

[+]-stepₗ : 𝐒(x) + y ≡ 𝐒(x + y)
[+]-stepₗ {x}{y} = ℕ-elim _ [≡]-intro (i ↦ congruence₁(𝐒) {𝐒(x) + i} {x + 𝐒(i)}) y
{-# REWRITE [+]-stepₗ #-}

[+]-stepᵣ : x + 𝐒(y) ≡ 𝐒(x + y)
[+]-stepᵣ = [≡]-intro
