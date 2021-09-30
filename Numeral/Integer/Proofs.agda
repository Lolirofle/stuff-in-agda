module Numeral.Integer.Proofs where

import      Lvl
open import Numeral.Integer
open import Numeral.Natural as ℕ using (ℕ)
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function.Domain
open import Type

private variable ℓ : Lvl.Level

[−𝐒ₙ]-equality : ∀{n} → (−𝐒ₙ(n) ≡ −ₙ(ℕ.𝐒(n)))
[−𝐒ₙ]-equality = [≡]-intro

[+𝐒ₙ]-equality : ∀{n} → (+𝐒ₙ(n) ≡ +ₙ(ℕ.𝐒(n)))
[+𝐒ₙ]-equality = [≡]-intro

instance
  [+ₙ]-injectivity : Injective(+ₙ_)
  Injective.proof [+ₙ]-injectivity [≡]-intro = [≡]-intro

instance
  [−𝐒ₙ]-injectivity : Injective(−𝐒ₙ_)
  Injective.proof [−𝐒ₙ]-injectivity [≡]-intro = [≡]-intro

instance
  [−ₙ]-injectivity : Injective(−ₙ_)
  Injective.proof [−ₙ]-injectivity {ℕ.𝟎}   {ℕ.𝟎}    xy        = [≡]-intro
  Injective.proof [−ₙ]-injectivity {ℕ.𝐒 x} {ℕ.𝐒 .x} [≡]-intro = [≡]-intro

instance
  [+𝐒ₙ]-injectivity : Injective(+𝐒ₙ_)
  Injective.proof [+𝐒ₙ]-injectivity [≡]-intro = [≡]-intro

absₙ-zero : ∀{n} → (absₙ(n) ≡ ℕ.𝟎) → (n ≡ 𝟎)
absₙ-zero {𝟎} [≡]-intro = [≡]-intro

absₙ-of-[−ₙ] : ∀{x} → (absₙ(−ₙ x) ≡ x)
absₙ-of-[−ₙ] {ℕ.𝟎}   = [≡]-intro
absₙ-of-[−ₙ] {ℕ.𝐒 x} = [≡]-intro
