module Numeral.Integer.Function.Proofs.Simple where

import      Lvl
open import Numeral.Integer
open import Numeral.Integer.Function
open import Numeral.Natural as ℕ using (ℕ)
open import Relator.Equals

-- (−n)−1 = −(n+1)
[𝐏]-negative : ∀{n} → (𝐏(−ₙ n) ≡ −𝐒ₙ(n))
[𝐏]-negative {ℕ.𝟎}    = [≡]-intro
[𝐏]-negative {ℕ.𝐒(n)} = [≡]-intro

-- (−(n+1))+1 = −n
[𝐒][−𝐒ₙ]-negative-identity : ∀{n} → (𝐒(−𝐒ₙ(n)) ≡ −ₙ n)
[𝐒][−𝐒ₙ]-negative-identity {ℕ.𝟎}    = [≡]-intro
[𝐒][−𝐒ₙ]-negative-identity {ℕ.𝐒(n)} = [≡]-intro

[−𝐒][−𝐒ₙ]-identity : ∀{n} → (− 𝐒(+ₙ n) ≡ −𝐒ₙ(n))
[−𝐒][−𝐒ₙ]-identity {n} = [≡]-intro
