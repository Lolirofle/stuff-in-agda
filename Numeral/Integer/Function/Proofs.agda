module Numeral.Integer.Function.Proofs where

import      Lvl
open import Numeral.Integer
open import Numeral.Integer.Construction
open import Numeral.Integer.Construction.Proofs
open import Numeral.Integer.Function
open import Numeral.Integer.Sign
open import Numeral.Natural as ℕ using (ℕ)
import      Numeral.Sign as Sign
open import Logic.Predicate
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Function.Multi
open import Structure.Relator.Properties
open import Syntax.Transitivity

open import Numeral.Integer.Function.Proofs.Simple public

private variable ℓ : Lvl.Level

instance
  [+ₙ][𝐒]-preserving : Preserving₁(+ₙ_) ℕ.𝐒 𝐒
  [+ₙ][𝐒]-preserving = intro [≡]-intro

instance
  [−ₙ][𝐒][𝐏]-preserving : Preserving₁(−ₙ_) ℕ.𝐒 𝐏
  Preserving.proof [−ₙ][𝐒][𝐏]-preserving {ℕ.𝟎}   = [≡]-intro
  Preserving.proof [−ₙ][𝐒][𝐏]-preserving {ℕ.𝐒 x} = [≡]-intro

instance
  [−][𝐒][𝐏]-preserving : Preserving₁(−_) 𝐒 𝐏
  Preserving.proof [−][𝐒][𝐏]-preserving {+ₙ ℕ.𝟎}    = [≡]-intro
  Preserving.proof [−][𝐒][𝐏]-preserving {+ₙ ℕ.𝐒 x}  = [≡]-intro
  Preserving.proof [−][𝐒][𝐏]-preserving {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
  Preserving.proof [−][𝐒][𝐏]-preserving {−𝐒ₙ ℕ.𝐒 x} = [≡]-intro

instance
  [−𝐒ₙ][𝐒][𝐏]-preserving : Preserving₁(−𝐒ₙ_) ℕ.𝐒 𝐏
  Preserving.proof [−𝐒ₙ][𝐒][𝐏]-preserving = [≡]-intro

instance
  [+𝐒ₙ][𝐒]-preserving : Preserving₁(+𝐒ₙ_) ℕ.𝐒 𝐒
  Preserving.proof [+𝐒ₙ][𝐒]-preserving = [≡]-intro
  
[−ₙ]-distribute-[−] : ∀{x y} → (−(x −ₙ y) ≡ y −ₙ x)
[−ₙ]-distribute-[−] {ℕ.𝟎}   {ℕ.𝟎}   = [≡]-intro
[−ₙ]-distribute-[−] {ℕ.𝟎}   {ℕ.𝐒 x} = [≡]-intro
[−ₙ]-distribute-[−] {ℕ.𝐒 x} {ℕ.𝟎}   = [≡]-intro
[−ₙ]-distribute-[−] {ℕ.𝐒 x} {ℕ.𝐒 y} = [−ₙ]-distribute-[−] {x} {y}

[−][−ₙ] : ∀{x} → (−(+ₙ x) ≡ −ₙ x)
[−][−ₙ] {ℕ.𝟎}    = [≡]-intro
[−][−ₙ] {ℕ.𝐒(_)} = [≡]-intro

[−ₙ][𝐒]-step : ∀{x y} → (ℕ.𝐒(x) −ₙ y ≡ 𝐒(x −ₙ y))
[−ₙ][𝐒]-step {ℕ.𝟎}   {ℕ.𝟎}    = [≡]-intro
[−ₙ][𝐒]-step {ℕ.𝟎}   {ℕ.𝐒(y)} = [−ₙ]-antiidentityₗ {y} 🝖 symmetry(_≡_) ([𝐒][−𝐒ₙ]-negative-identity{y})
[−ₙ][𝐒]-step {ℕ.𝐒(_)}{ℕ.𝟎}    = [≡]-intro
[−ₙ][𝐒]-step {ℕ.𝐒(x)}{ℕ.𝐒(y)} = [−ₙ][𝐒]-step {x}{y}

sign-of-signed-𝐒 : ∀{s}{n} → (sign(signed s (ℕ.𝐒(n))) ≡ s)
sign-of-signed-𝐒 {Sign.➕} = [≡]-intro
sign-of-signed-𝐒 {Sign.➖} = [≡]-intro

sign0-of-signed-𝐒 : ∀{s}{n} → (sign0(signed s (ℕ.𝐒(n))) ≡ Sign.zeroable(s))
sign0-of-signed-𝐒 {Sign.➕} = [≡]-intro
sign0-of-signed-𝐒 {Sign.➖} = [≡]-intro

instance
  [−]-involution : Involution(−_)
  Involution.proof [−]-involution {+ₙ ℕ.𝟎}    = [≡]-intro
  Involution.proof [−]-involution {+ₙ ℕ.𝐒(x)} = [≡]-intro
  Involution.proof [−]-involution {−𝐒ₙ x}     = [≡]-intro

instance
  [−]-injectivity : Injective(−_)
  Injective.proof [−]-injectivity {a}{b} p =
    a      🝖[ _≡_ ]-[ involution(−_) ]-sym
    −(− a) 🝖[ _≡_ ]-[ congruence₁(−_) p ]
    −(− b) 🝖[ _≡_ ]-[ involution(−_) ]
    b      🝖-end

instance
  [−]-surjectivity : Surjective(−_)
  Surjective.proof [−]-surjectivity {y} = [∃]-intro (− y) ⦃ involution(−_) ⦄

instance
  [−]-bijectivity : Bijective(−_)
  [−]-bijectivity = injective-surjective-to-bijective(−_)

instance
  abs-idempotent : Idempotent(abs)
  Idempotent.proof abs-idempotent {+ₙ x}  = [≡]-intro
  Idempotent.proof abs-idempotent {−𝐒ₙ x} = [≡]-intro

abs-injective-zero : ∀{n} → (abs(n) ≡ 𝟎) → (n ≡ 𝟎)
abs-injective-zero {𝟎} [≡]-intro = [≡]-intro

abs-[−] : ∀{n} → (abs(− n) ≡ abs(n))
abs-[−] {𝟎}      = [≡]-intro
abs-[−] {+𝐒ₙ(_)} = [≡]-intro
abs-[−] {−𝐒ₙ(_)} = [≡]-intro

abs-preserving : ∀{x} → (abs(x) ≡ +ₙ(absₙ(x)))
abs-preserving {𝟎}      = [≡]-intro
abs-preserving {+𝐒ₙ(_)} = [≡]-intro
abs-preserving {−𝐒ₙ(_)} = [≡]-intro

signed-inverse : ∀{x} → (signed0 (sign0 x) (absₙ x) ≡ x)
signed-inverse {+𝐒ₙ _} = [≡]-intro
signed-inverse {𝟎}     = [≡]-intro
signed-inverse {−𝐒ₙ _} = [≡]-intro

sign0-inverse : ∀{x}{y} → (sign0(signed0 x (ℕ.𝐒(y))) ≡ x)
sign0-inverse {Sign.➕} {y} = [≡]-intro
sign0-inverse {Sign.𝟎}  {y} = [≡]-intro
sign0-inverse {Sign.➖} {y} = [≡]-intro

absₙ-inverse : ∀{x}{y} → (x ≢ Sign.𝟎) → (absₙ(signed0 x y) ≡ y)
absₙ-inverse {Sign.➕} {ℕ.𝟎}   _ = [≡]-intro
absₙ-inverse {Sign.➕} {ℕ.𝐒 y} _ = [≡]-intro
absₙ-inverse {Sign.➖} {ℕ.𝟎}   _ = [≡]-intro
absₙ-inverse {Sign.➖} {ℕ.𝐒 y} _ = [≡]-intro
absₙ-inverse {Sign.𝟎} {ℕ.𝟎}    _ = [≡]-intro
absₙ-inverse {Sign.𝟎} {ℕ.𝐒 y}  p with () ← p [≡]-intro

absₙ-of-[−] : ∀{x} → (absₙ(− x) ≡ absₙ x)
absₙ-of-[−] {+𝐒ₙ _} = [≡]-intro
absₙ-of-[−] {𝟎}     = [≡]-intro
absₙ-of-[−] {−𝐒ₙ _} = [≡]-intro
