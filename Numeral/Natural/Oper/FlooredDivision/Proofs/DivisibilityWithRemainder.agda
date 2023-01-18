module Numeral.Natural.Oper.FlooredDivision.Proofs.DivisibilityWithRemainder where

open import Data
open import Functional
open import Numeral.Finite
import      Numeral.Finite.Proofs as 𝕟
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Algorithm
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.DivisibilityWithRemainder
open import Numeral.Natural.Relation.DivisibilityWithRemainder.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Syntax.Transitivity

-- The quotient of the divisibility relation is given by the floored division operation.
[⌊/⌋][∣ᵣₑₘ]-quotient-equality : ∀{x y} ⦃ pos : Positive(y) ⦄ {r}{p : (y ∣ᵣₑₘ x)(r)} → ((x ⌊/⌋ y) ≡ [∣ᵣₑₘ]-quotient p)
[⌊/⌋][∣ᵣₑₘ]-quotient-equality {𝟎}             {_}   {𝟎}   {DivRem𝟎} = [≡]-intro
[⌊/⌋][∣ᵣₑₘ]-quotient-equality {𝐒 .(toℕ r)} {𝐒(𝐒 y)} {𝐒 r} {DivRem𝟎} =
  ([ 0 , 𝐒(y) ] (toℕ r) div y) 🝖[ _≡_ ]-[ inddiv-lesser(𝕟.toℕ-bounded{𝐒 y}{r}) ]
  𝟎                               🝖-end
[⌊/⌋][∣ᵣₑₘ]-quotient-equality {𝐒 x} {𝐒 𝟎} {𝟎} {DivRem𝐒 p} = inddiv-result-𝐒 {0}{0}{x}{0} 🝖_ $ congruence₁(𝐒) $
  ([ 0 , 0 ] x div 0) 🝖[ _≡_ ]-[ [⌊/⌋]-of-1ᵣ ]
  x                   🝖[ _≡_ ]-[ [∣ᵣₑₘ]-quotient-of-1 p ]-sym
  [∣ᵣₑₘ]-quotient p   🝖-end
{-# CATCHALL #-}
[⌊/⌋][∣ᵣₑₘ]-quotient-equality {𝐒 .(x + y)} {𝐒 y} {r} {DivRem𝐒 {x = x} p} =
  ([ 0 , y ] (𝐒(x) + y) div y) 🝖[ _≡_ ]-[ inddiv-step-denominator{0}{(y)}{𝐒(x)}{y} ]
  ([ 0 , y ] 𝐒(x) div 𝟎)       🝖[ _≡_ ]-[ inddiv-result-𝐒 {0}{y}{x}{y} ]
  𝐒([ 0 , y ] x div y)         🝖[ _≡_ ]-[ congruence₁(𝐒) ([⌊/⌋][∣ᵣₑₘ]-quotient-equality {p = p}) ]
  𝐒([∣ᵣₑₘ]-quotient p)         🝖-end
