module Numeral.Integer.Induction where

open import Functional.Dependent
import      Lvl
open import Numeral.Integer
open import Numeral.Integer.Construction
open import Numeral.Integer.Function
open import Numeral.Integer.Function.Proofs.Simple
open import Numeral.Natural as ℕ using (ℕ)
open import Numeral.Natural.Induction
import      Numeral.Sign as Sign
open import Relator.Equals.Proofs
open import Type

private variable ℓ : Lvl.Level

ℤ-non-negative-recursion : (P : ℤ → Type{ℓ}) → P(𝟎) → (∀(n) → P(+ₙ(n)) → P(+𝐒ₙ(n))) → (∀(n) → P(+ₙ n))
ℤ-non-negative-recursion P = ℕ-elim(P ∘ +ₙ_)

ℤ-positive-recursion : (P : ℤ → Type{ℓ}) → P(+𝐒ₙ(ℕ.𝟎)) → (∀(n) → P(+𝐒ₙ(n)) → P(+𝐒ₙ(ℕ.𝐒(n)))) → (∀(n) → P(+𝐒ₙ n))
ℤ-positive-recursion P = ℕ-elim(P ∘ +𝐒ₙ_)

ℤ-non-positive-recursion : (P : ℤ → Type{ℓ}) → P(𝟎) → (∀(n) → P(−ₙ(n)) → P(−𝐒ₙ(n))) → (∀(n) → P(−ₙ n))
ℤ-non-positive-recursion P = ℕ-elim(P ∘ −ₙ_)

ℤ-negative-recursion : (P : ℤ → Type{ℓ}) → P(−𝐒ₙ(ℕ.𝟎)) → (∀(n) → P(−𝐒ₙ(n)) → P(−𝐒ₙ(ℕ.𝐒(n)))) → (∀(n) → P(−𝐒ₙ n))
ℤ-negative-recursion P = ℕ-elim(P ∘ −𝐒ₙ_)

-- An intuitive recursion proof method on integers splitting the integers into three cases: negatives, zero and positives.
ℤ-sign-recursion : (P : ℤ → Type{ℓ}) → (∀(n) → P(−ₙ n) → P(−𝐒ₙ(n))) → P(𝟎) → (∀(n) → P(+ₙ n) → P(+𝐒ₙ(n))) → (∀(n) → P(n))
ℤ-sign-recursion P [−] [0] [+] (+ₙ n)   = ℤ-non-negative-recursion P [0] [+] n
ℤ-sign-recursion P [−] [0] [+] (−𝐒ₙ(n)) = ℤ-negative-recursion P ([−] _ [0]) ([−] ∘ ℕ.𝐒) n

ℤ-signed-recursion : (P : ℤ → Type{ℓ}) → P(𝟎) → (∀(s)(n) → P(signed s n) → P(signed s (ℕ.𝐒(n)))) → (∀(n) → P(n))
ℤ-signed-recursion P zero step = ℤ-sign-recursion P (step(Sign.➖)) zero (step(Sign.➕))

-- An recursion proof method with similarities to the recursion for ℕ.
ℤ-signed-step-recursion : (P : ℤ → Type{ℓ}) → P(𝟎) → (∀(s)(n) → P(signed s n) → P(step s (signed s n))) → (∀(n) → P(n))
ℤ-signed-step-recursion P zero step = ℤ-sign-recursion P ([≡]-substitutionᵣ [𝐏]-negative {P} ∘₂ step(Sign.➖)) zero (step(Sign.➕))
