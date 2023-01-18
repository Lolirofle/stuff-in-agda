module Numeral.Natural.Oper.Modulo.Proofs.DivisibilityWithRemainder where

open import Data
open import Functional
open import Numeral.Finite
import      Numeral.Finite.Proofs as 𝕟
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Modulo.Proofs.Algorithm
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.DivisibilityWithRemainder
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Relator
open import Syntax.Transitivity

-- The remainder of the divisibility relation is given by the modulo operation.
[mod][∣ᵣₑₘ]-remainder-equality : ∀{x y} ⦃ pos : Positive(y) ⦄ {r}{p : (y ∣ᵣₑₘ x)(r)} → ((x mod y) ≡ toℕ ([∣ᵣₑₘ]-remainder p))
[mod][∣ᵣₑₘ]-remainder-equality {𝟎}             {𝐒 _}    {𝟎}   {DivRem𝟎}   = [≡]-intro
[mod][∣ᵣₑₘ]-remainder-equality {𝐒 .(toℕ r)} {𝐒(𝐒 y)} {𝐒 r} {DivRem𝟎}   = mod'-lesser-dividend {1}{𝐒(y)}{toℕ r}{y} ([≤]-without-[𝐒] 𝕟.toℕ-bounded)
[mod][∣ᵣₑₘ]-remainder-equality {𝐒 x}           {𝐒 𝟎}    {𝟎}   {DivRem𝐒 p} = mod'-zero-all-except-dividend {x}
{-# CATCHALL #-}
[mod][∣ᵣₑₘ]-remainder-equality {𝐒 .(x + y)}    {𝐒 y}    {r}   {DivRem𝐒 {x = x} p} =
  ([ 𝟎 , y ] 𝐒(x + y) mod' y)           🝖[ _≡_ ]-[]
  ([ 𝟎 , y ] (𝐒(x) + y) mod' y)         🝖[ _≡_ ]-[ mod'-sumᵣ-modulo {0}{y}{x}{y} ]
  ([ 𝟎 , y ] x mod' y)                  🝖[ _≡_ ]-[ [mod][∣ᵣₑₘ]-remainder-equality {p = p} ]
  toℕ ([∣ᵣₑₘ]-remainder p)           🝖[ _≡_ ]-[]
  toℕ ([∣ᵣₑₘ]-remainder (DivRem𝐒 p)) 🝖-end
