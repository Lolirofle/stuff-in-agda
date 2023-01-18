module Numeral.Finite.Oper.Bounded.Proofs.𝐏 where

open import Data
open import Numeral.Finite
import      Numeral.Finite.Oper.Bounded as Bounded
import      Numeral.Finite.Relation as 𝕟
import      Numeral.Finite.Relation.Order as 𝕟
import      Numeral.Finite.Relation.Order.Proofs as 𝕟
open import Numeral.Natural
import      Numeral.Natural.Relation as ℕ
import      Numeral.Natural.Relation.Order.Proofs as ℕ
open import Relator.Equals

𝐏-step : ∀{X Y} ⦃ pos-Y : ℕ.Positive(Y) ⦄ {x : 𝕟(X)} ⦃ pos : 𝕟.Positive(x) ⦄ → (Bounded.𝐏(𝐒(x)) ≡ 𝐒(Bounded.𝐏{b₂ = Y}(x)))
𝐏-step {Y = 𝐒 Y} {x = 𝐒 x} = [≡]-intro

bounded-𝐏-𝐒-inverses : ∀{N₁ N₂} ⦃ pos : ℕ.Positive(N₂) ⦄ {x : 𝕟(N₁)} → (x 𝕟.≤ maximum{N₂}) → (Bounded.𝐏 {b₂ = N₂} ⦃ pos ⦄ (𝐒(x)) 𝕟.≡ x)
bounded-𝐏-𝐒-inverses {N₂ = 𝐒 𝟎}   {x = 𝟎}   _   = <>
bounded-𝐏-𝐒-inverses {N₂ = 𝐒 𝟎}   {x = 𝐒 _} ()
bounded-𝐏-𝐒-inverses {N₂ = 𝐒(𝐒 n)}{x = 𝟎}   _   = <>
bounded-𝐏-𝐒-inverses {N₂ = 𝐒(𝐒 n)}{x = 𝐒 x} ord = bounded-𝐏-𝐒-inverses{N₂ = 𝐒 n}{x = x} ord

𝐒-bounded-𝐏-inverses : ∀{N₁ N₂} ⦃ pos-n : ℕ.Positive(N₂) ⦄ {x : 𝕟(N₁)} → ⦃ pos-x : 𝕟.Positive(x) ⦄ → (x 𝕟.≤ maximum{𝐒(N₂)}) → (𝐒(Bounded.𝐏 {b₂ = N₂} (x)) 𝕟.≡ x)
𝐒-bounded-𝐏-inverses {N₂ = 𝐒 𝟎}   {x = 𝐒 𝟎}    _   = <>
𝐒-bounded-𝐏-inverses {N₂ = 𝐒 𝟎}   {x = 𝐒(𝐒 _)} ()
𝐒-bounded-𝐏-inverses {N₂ = 𝐒(𝐒 n)}{x = 𝐒 𝟎}    _   = <>
𝐒-bounded-𝐏-inverses {N₂ = 𝐒(𝐒 n)}{x = 𝐒(𝐒 x)} ord = 𝐒-bounded-𝐏-inverses {N₂ = 𝐒 n}{x = 𝐒 x} ord

bounded-𝐏-𝐒-preserving : ∀{N Nₗ Nᵣ} ⦃ posₗ : ℕ.Positive(Nₗ) ⦄ ⦃ posᵣ : ℕ.Positive(Nᵣ) ⦄ {x : 𝕟(N)} → ⦃ pos-x : 𝕟.Positive(x) ⦄ → (x 𝕟.≤ maximum{Nₗ}) → (x 𝕟.≤ maximum{𝐒(Nᵣ)}) → (Bounded.𝐏 {b₂ = Nₗ} (𝐒(x)) 𝕟.≡ 𝐒(Bounded.𝐏 {b₂ = Nᵣ} (x)))
bounded-𝐏-𝐒-preserving {N}{Nₗ}{Nᵣ}{x} ordₗ ordᵣ = 𝕟.[≡]-transitivity-raw {Nₗ}{a = Bounded.𝐏 _}
  (bounded-𝐏-𝐒-inverses {x = x} ordₗ)
  (𝕟.[≡]-symmetry-raw {b = x} (𝐒-bounded-𝐏-inverses {x = x} ordᵣ))
