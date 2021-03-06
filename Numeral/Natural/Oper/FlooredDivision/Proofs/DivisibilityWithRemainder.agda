module Numeral.Natural.Oper.FlooredDivision.Proofs.DivisibilityWithRemainder where

open import Data
open import Functional
open import Numeral.Finite
import      Numeral.Finite.Proofs as 𝕟
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs
open import Numeral.Natural.Relation.DivisibilityWithRemainder hiding (base₀ ; base₊ ; step)
open import Numeral.Natural.Relation.DivisibilityWithRemainder.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Syntax.Transitivity

-- The quotient of the divisibility relation is given by the floored division operation.
[⌊/⌋][∣ᵣₑₘ]-quotient-equality : ∀{x y r}{p : (𝐒(y) ∣ᵣₑₘ x)(r)} → ((x ⌊/⌋ 𝐒(y)) ≡ [∣ᵣₑₘ]-quotient p)
[⌊/⌋][∣ᵣₑₘ]-quotient-equality {𝟎}             {_}   {𝟎}   {DivRem𝟎} = [≡]-intro
[⌊/⌋][∣ᵣₑₘ]-quotient-equality {𝐒 .(𝕟-to-ℕ r)} {𝐒 y} {𝐒 r} {DivRem𝟎} =
  ([ 0 , 𝐒(y) ] (𝕟-to-ℕ r) div y) 🝖[ _≡_ ]-[ inddiv-smaller(𝕟.bounded{y}{r}) ]
  𝟎                               🝖-end
[⌊/⌋][∣ᵣₑₘ]-quotient-equality {𝐒 x} {𝟎} {𝟎} {DivRem𝐒 p} = [≡]-with(𝐒) $
  ([ 0 , 0 ] x div 0) 🝖[ _≡_ ]-[ [⌊/⌋]-of-1ᵣ ]
  x                   🝖[ _≡_ ]-[ [∣ᵣₑₘ]-quotient-of-1 p ]-sym
  [∣ᵣₑₘ]-quotient p   🝖-end
{-# CATCHALL #-}
[⌊/⌋][∣ᵣₑₘ]-quotient-equality {𝐒 .(x + y)} {y} {r} {DivRem𝐒 {x = x} p} =
  ([ 0 , (y) ] (𝐒(x) + y) div y) 🝖[ _≡_ ]-[ inddiv-step-denominator{0}{(y)}{𝐒(x)}{y} ]
  ([ 0 , (y) ] 𝐒(x) div 𝟎)       🝖[ _≡_ ]-[]
  𝐒([ 0 , y ] x div y)           🝖[ _≡_ ]-[ [≡]-with(𝐒) ([⌊/⌋][∣ᵣₑₘ]-quotient-equality {p = p}) ]
  𝐒([∣ᵣₑₘ]-quotient p)           🝖-end
