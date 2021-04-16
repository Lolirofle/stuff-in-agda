module Numeral.Natural.Proofs where

import Lvl
open import Numeral.Natural
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain

private variable n : ℕ

[𝐒]-not-0 : (𝐒(n) ≢ 𝟎)
[𝐒]-not-0 ()

𝐒-not-self : (𝐒(n) ≢ n)
𝐒-not-self ()

instance
  [𝐒]-injectivity : Injective(𝐒)
  Injective.proof([𝐒]-injectivity) = congruence₁(𝐏)

instance
  [𝐏][𝐒]-inverseᵣ : Inverseᵣ(𝐏)(𝐒)
  [𝐏][𝐒]-inverseᵣ = intro [≡]-intro
