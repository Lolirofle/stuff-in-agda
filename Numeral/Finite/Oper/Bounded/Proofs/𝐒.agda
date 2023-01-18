module Numeral.Finite.Oper.Bounded.Proofs.𝐒 where

open import Data
open import Functional
open import Logic.Propositional
open import Numeral.Finite
import      Numeral.Finite.Oper.Bounded as Bounded
import      Numeral.Finite.Relation.Order as 𝕟
open import Numeral.Natural
import      Numeral.Natural.Relation as ℕ

bounded-𝐒-is-𝐒 : ∀{N₁}{N₂} ⦃ pos₂ : ℕ.Positive(N₂) ⦄ {n : 𝕟(N₁)} → (n 𝕟.< maximum{N₂}) ↔ (Bounded.𝐒{N₁}{N₂} (n) 𝕟.≡ 𝐒(n))
bounded-𝐒-is-𝐒 {𝐒 N₁}{𝐒 𝟎}     {n = 𝟎}   = [↔]-intro (\()) (\())
bounded-𝐒-is-𝐒 {𝐒 N₁}{𝐒 𝟎}     {n = 𝐒 n} = [↔]-intro (\()) (\())
bounded-𝐒-is-𝐒 {𝐒 N₁}{𝐒(𝐒 N₂)} {n = 𝟎}   = [↔]-intro (const <>) (const <>)
bounded-𝐒-is-𝐒 {𝐒 N₁}{𝐒(𝐒 N₂)} {n = 𝐒 n} = bounded-𝐒-is-𝐒 {N₁} {𝐒 N₂} {n = n}
