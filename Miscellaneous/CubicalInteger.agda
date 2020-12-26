{-# OPTIONS --cubical #-}

module Miscellaneous.CubicalInteger where

import      Lvl
open import Numeral.Natural as ℕ using (ℕ)
open import Numeral.Sign as Sign using (−|+ ; −|0|+ ; ➖ ; ➕)
open import Type.Cubical
open import Type.Cubical.Equality
open import Type

apply : ∀{ℓ}{T : Type{ℓ}}{x y : T} → Interval → (x ≡ y) → T
apply i xy = xy i

infix 10010 −ₙ_ +ₙ_
infix 10020 _+_ _−_

-- The type of integers ℤ = {…,−2,−1,0,1,2,…}.
-- Represented by using the exclusive union of ℕ and ℕ, but the zeroes are equal.
data ℤ : Type{Lvl.𝟎} where
  signed : (−|+) → ℕ → ℤ
  𝟎-sign : (signed ➖ ℕ.𝟎 ≡ signed ➕ ℕ.𝟎)

-- Intuitive constructor patterns
-- −ₙ_ : ℕ → ℤ
-- +ₙ_ : ℕ → ℤ
pattern −ₙ_ n = signed ➖ n
pattern +ₙ_ n = signed ➕ n
pattern 𝟎  = +ₙ(ℕ.𝟎) -- Zero (0).
pattern 𝟏  = +ₙ(ℕ.𝟏) -- One (1).
pattern −𝟏 = −ₙ(ℕ.𝟏) -- Negative one (−1).

open import Structure.Relator.Properties
open import Type.Cubical.Path
open import Type.Cubical.Path.Proofs

module _ where
  open import Type.Isomorphism
  postulate univalence : ∀{ℓ}{A B : Type{ℓ}} → (A ≅ B) ≅ (A ≡ B)

elim : ∀{ℓ} → (P : ℤ → Type{ℓ}) → (neg : (n : ℕ) → P(−ₙ n)) → (pos : (n : ℕ) → P(+ₙ n)) → PathP(pointOn(map P 𝟎-sign)) (neg ℕ.𝟎) (pos ℕ.𝟎) → ((n : ℤ) → P(n))
elim(P) neg _   eq (−ₙ n) = neg n
elim(P) _   pos eq (+ₙ n) = pos n
elim(P) _   _   eq (𝟎-sign i) = eq i

-- Sign.
-- The sign part of an integer where zero is interpreted as positive.
-- Notes on the proof of the path:
--   The 𝟎-sign case guarantees that the function respects the congruence property (in this case (−0 = +0) → (sign(−0) = sign(+0))).
--   It is proven by providing the value on a path varying on the variable `i`. In this case, it is constant (both −0 and +0 maps to ➕).
sign : ℤ → (−|+)
sign (signed _ ℕ.𝟎)      = ➕
sign (signed s (ℕ.𝐒(_))) = s
sign (𝟎-sign i) = ➕

-- Zeroable sign.
sign₀ : ℤ → (−|0|+)
sign₀ (signed s ℕ.𝟎)      = Sign.𝟎
sign₀ (signed s (ℕ.𝐒(_))) = Sign.zeroable s
sign₀ (𝟎-sign i) = Sign.𝟎

-- Absolute value.
-- The natural part of an integer.
absₙ : ℤ → ℕ
absₙ(−ₙ n) = n
absₙ(+ₙ n) = n
absₙ(𝟎-sign _) = ℕ.𝟎

open import Data.Either
open import Functional using (_$_)
open import Logic.Propositional
import      Numeral.Sign.Oper as Sign
open import Relator.Equals using () renaming (_≡_ to Id ; [≡]-intro to Id-intro)
open import Relator.Equals.Proofs.Equivalence using () renaming ([≡]-equiv to Id-equiv ; [≡]-symmetry to Id-symmetry ; [≡]-to-function to Id-to-function ; [≡]-function to Id-function)
open import Syntax.Transitivity

Sign-decidable-eq : ∀(s₁ s₂ : (−|+)) → (Id s₁ s₂ ∨ ¬(Id s₁ s₂))
Sign-decidable-eq ➕ ➕ = [∨]-introₗ Id-intro
Sign-decidable-eq ➕ ➖ = [∨]-introᵣ \()
Sign-decidable-eq ➖ ➕ = [∨]-introᵣ \()
Sign-decidable-eq ➖ ➖ = [∨]-introₗ Id-intro

step : (−|+) → ℤ → ℤ
step s₁ (signed s₂ n) with Sign-decidable-eq s₁ s₂
step _  (signed s n)         | Left  _ = signed s (ℕ.𝐒(n))
step s₁ (signed s₂ ℕ.𝟎)      | Right _ = signed s₁ (ℕ.𝐒(ℕ.𝟎))
step s₁ (signed s₂ (ℕ.𝐒(n))) | Right _ = signed s₂ n
step ➕ (𝟎-sign i) = reflexivity (_≡_) {𝟏} i
step ➖ (𝟎-sign i) = reflexivity (_≡_) {−𝟏} i

-- Predecessor.
-- Alternative implementation:
--   𝐏(−ₙ n)      = −ₙ(ℕ.𝐒(n))
--   𝐏(+ₙ ℕ.𝟎)    = −ₙ(ℕ.𝐒(ℕ.𝟎))
--   𝐏(+ₙ(ℕ.𝐒 n)) = +ₙ n
--   𝐏(𝟎-sign i)  = reflexivity(_≡_) {−𝟏} i
𝐏 : ℤ → ℤ
𝐏 = step ➖

-- Successor.
-- Alternative implementation:
--   𝐒(−ₙ(ℕ.𝐒 n)) = −ₙ n
--   𝐒(−ₙ ℕ.𝟎)    = +ₙ(ℕ.𝐒(ℕ.𝟎))
--   𝐒(+ₙ n)      = +ₙ(ℕ.𝐒(n))
--   𝐒(𝟎-sign i)  = reflexivity(_≡_) {𝟏} i
𝐒 : ℤ → ℤ
𝐒 = step ➕

-- Negation.
−_ : ℤ → ℤ
−(signed s n) = signed (Sign.− s) n
−(𝟎-sign i) = symmetry(_≡_) 𝟎-sign i

-- Absolute value.
abs : ℤ → ℤ
abs(signed _ n) = signed ➕ n
abs(𝟎-sign i) = reflexivity(_≡_) {𝟎} i

-- Addition.
_+_ : ℤ → ℤ → ℤ
x + (signed _ ℕ.𝟎)      = x
x + (signed s (ℕ.𝐒(y))) = step s (x + (signed s y))
x + 𝟎-sign i = reflexivity(_≡_) {x} i

-- Subtraction.
_−_ : ℤ → ℤ → ℤ
x − y = x + (− y)

𝟎-signs : ∀{s₁ s₂} → (signed s₁ ℕ.𝟎 ≡ signed s₂ ℕ.𝟎)
𝟎-signs {➕} {➕} = reflexivity(_≡_)
𝟎-signs {➕} {➖} = symmetry(_≡_) 𝟎-sign
𝟎-signs {➖} {➕} = 𝟎-sign
𝟎-signs {➖} {➖} = reflexivity(_≡_)

-- Notes on the proof of the path:
--   𝐏(𝟎-sign i) = −𝟏
--   𝐒(𝐏(𝟎-sign i)) = 𝐒(−𝟏) = −𝟎
--   and
--   • i=0: const(−ₙ 0) j = −ₙ 0
--   • i=1: 𝟎-sign j
--   • j=0: −ₙ 0
--   • j=1: 𝟎-sign i
--   which means:
--   • i=0 ∧ j=0: −0 , −0
--   • i=0 ∧ j=1: −0 , −0
--   • i=1 ∧ j=0: −0 , −0
--   • i=1 ∧ j=1: +0 , +0
--   The value varies between −0 and +0. Therefore, a path between them should be used: 𝟎-sign.
--   It is −𝟎 when i or j is 0 and +𝟎 when i and j is 0. Therefore, min.
𝐒-𝐏-inverses : ∀{n} → (𝐒(𝐏(n)) ≡ n)
𝐒-𝐏-inverses {+ₙ(ℕ.𝟎)}    = 𝟎-sign
𝐒-𝐏-inverses {+ₙ(ℕ.𝐒(x))} = reflexivity(_≡_)
𝐒-𝐏-inverses {−ₙ x}       = reflexivity(_≡_)
𝐒-𝐏-inverses {𝟎-sign i} j = 𝟎-sign (Interval.min i j)

𝐏-𝐒-inverses : ∀{n} → (𝐏(𝐒(n)) ≡ n)
𝐏-𝐒-inverses {−ₙ(ℕ.𝟎)}    = symmetry(_≡_) 𝟎-sign
𝐏-𝐒-inverses {−ₙ(ℕ.𝐒(x))} = reflexivity(_≡_)
𝐏-𝐒-inverses {+ₙ x}       = reflexivity(_≡_)
𝐏-𝐒-inverses {𝟎-sign i} j = 𝟎-sign (Interval.max i (Interval.flip j))

step-inverses : ∀{s₁ s₂}{n} → ¬(Id s₁ s₂) → (step s₁ (step s₂ n) ≡ n)
step-inverses {➕} {➕} eq with () ← eq Id-intro
step-inverses {➕} {➖} eq = 𝐒-𝐏-inverses
step-inverses {➖} {➕} eq = 𝐏-𝐒-inverses
step-inverses {➖} {➖} eq with () ← eq Id-intro

open import Structure.Function.Domain

{- TODO: Is something similar to this possible? Maybe (rel = ∀{x} → Unique(P(x))) instead?
induction : ∀{ℓ} → (P : ℤ → Type{ℓ}) → (∀{x y} → (x ≡ y) → P(x) → P(y)) → ((n : ℕ) → P(−ₙ n)) → P(𝟎) → ((n : ℕ) → P(+ₙ n)) → ((n : ℤ) → P(n))
induction(P) rel neg zero pos n = elim(P) neg pos ? n
-}

open import Functional using (_∘_)
import      Numeral.Sign.Proofs as Sign
open import Structure.Function
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Operator

𝐒-to-step : ∀{s}{n} → (signed s (ℕ.𝐒(n)) ≡ step s (signed s n))
𝐒-to-step {➕} {n} = reflexivity(_≡_)
𝐒-to-step {➖} {n} = reflexivity(_≡_)

step-swap : ∀{s₁ s₂}{x} → (step s₁ (step s₂ x) ≡ step s₂ (step s₁ x))
step-swap {➕} {➕} {x} = reflexivity(_≡_)
step-swap {➕} {➖} {x} = 𝐒-𝐏-inverses {x} 🝖 symmetry(_≡_) 𝐏-𝐒-inverses
step-swap {➖} {➕} {x} = 𝐏-𝐒-inverses {x} 🝖 symmetry(_≡_) 𝐒-𝐏-inverses
step-swap {➖} {➖} {x} = reflexivity(_≡_)

[+]ᵣ-of-step : ∀{s}{x y} → (x + step s(y) ≡ step s(x + y))
[+]ᵣ-of-step {s₁}{x} {signed s₂ n} with Sign-decidable-eq s₁ s₂
[+]ᵣ-of-step {s} {x} {signed s n} | Left Id-intro = reflexivity(_≡_)
[+]ᵣ-of-step {➕} {x} {signed ➕ n}       | Right p with () ← p Id-intro
[+]ᵣ-of-step {➕} {x} {signed ➖ ℕ.𝟎}     | Right _ = reflexivity(_≡_)
[+]ᵣ-of-step {➖} {x} {signed ➕ ℕ.𝟎}     | Right _ = reflexivity(_≡_)
[+]ᵣ-of-step {➕} {x} {signed ➖ (ℕ.𝐒 n)} | Right _ = symmetry(_≡_) 𝐒-𝐏-inverses
[+]ᵣ-of-step {➖} {x} {signed ➕ (ℕ.𝐒 n)} | Right _ = symmetry(_≡_) 𝐏-𝐒-inverses
[+]ᵣ-of-step {➖} {x} {signed ➖ n}       | Right p with () ← p Id-intro
[+]ᵣ-of-step {➕} {x} {𝟎-sign i} = reflexivity(_≡_)
[+]ᵣ-of-step {➖} {x} {𝟎-sign i} = reflexivity(_≡_)

[+]ₗ-of-step : ∀{s}{x y} → (step s(x) + y ≡ step s(x + y))
[+]ₗ-of-step {s₁} {x} {signed s₂ ℕ.𝟎} = reflexivity(_≡_)
[+]ₗ-of-step {s₁} {x} {signed s₂ (ℕ.𝐒 n)} =
  step s₁ x + signed s₂ (ℕ.𝐒 n)       🝖[ _≡_ ]-[]
  step s₂ (step s₁ x + signed s₂ n)   🝖[ _≡_ ]-[ congruence₂ᵣ(step)(s₂) ([+]ₗ-of-step {s₁} {x} {signed s₂ n}) ]
  step s₂ (step s₁ (x + signed s₂ n)) 🝖[ _≡_ ]-[ step-swap{s₂}{s₁}{x + signed s₂ n} ]
  step s₁ (step s₂ (x + signed s₂ n)) 🝖[ _≡_ ]-[ congruence₂ᵣ(step)(s₁) ([+]ᵣ-of-step {s₂} {x} {signed s₂ n}) ]-sym
  step s₁ (x + step s₂ (signed s₂ n)) 🝖[ _≡_ ]-[ congruence₂ᵣ(step)(s₁) (congruence₂ᵣ(_+_)(x) (𝐒-to-step {s₂}{n})) ]-sym
  step s₁ (x + signed s₂ (ℕ.𝐒 n))     🝖-end
[+]ₗ-of-step {➕} {signed ➕ ℕ.𝟎} {𝟎-sign i} j = 𝟏
[+]ₗ-of-step {➕} {signed ➖ ℕ.𝟎} {𝟎-sign i} j = 𝟏
[+]ₗ-of-step {➖} {signed ➕ ℕ.𝟎} {𝟎-sign i} j = −𝟏
[+]ₗ-of-step {➖} {signed ➖ ℕ.𝟎} {𝟎-sign i} j = −𝟏
[+]ₗ-of-step {➕} {signed ➕ (ℕ.𝐒 n)} {𝟎-sign i} j = +ₙ (ℕ.𝐒(ℕ.𝐒 n))
[+]ₗ-of-step {➕} {signed ➖ (ℕ.𝐒 n)} {𝟎-sign i} j = −ₙ n
[+]ₗ-of-step {➖} {signed ➕ (ℕ.𝐒 n)} {𝟎-sign i} j = +ₙ n
[+]ₗ-of-step {➖} {signed ➖ (ℕ.𝐒 n)} {𝟎-sign i} j = −ₙ (ℕ.𝐒(ℕ.𝐒 n))
[+]ₗ-of-step {➕} {𝟎-sign i₁} {𝟎-sign i} j = 𝟏
[+]ₗ-of-step {➖} {𝟎-sign i₁} {𝟎-sign i} j = −𝟏

instance
  [−]-involution : Involution(−_)
  Involution.proof [−]-involution {signed s n} rewrite involution(Sign.−_) {s} = reflexivity(_≡_)
  Involution.proof [−]-involution {𝟎-sign i} = reflexivity(_≡_)

instance
  [+]-commutativity : Commutativity(_+_)
  Commutativity.proof [+]-commutativity {x}{y} = p{x}{y} where
    p : Names.Commutativity(_+_)
    ps : ∀{x}{s}{n} → (x + signed s (ℕ.𝐒 n) ≡ signed s (ℕ.𝐒 n) + x)
    ps {x}{s}{n} =
      (x + signed s (ℕ.𝐒 n))   🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(_) (𝐒-to-step{s}{n}) ]
      (x + step s(signed s n)) 🝖[ _≡_ ]-[ [+]ᵣ-of-step {s}{x}{signed s n} ]
      step s(x + signed s n)   🝖[ _≡_ ]-[ congruence₂ᵣ(step)(s) (p {x} {signed s n}) ]
      step s(signed s n + x)   🝖[ _≡_ ]-[ [+]ₗ-of-step {s}{signed s n}{x} ]-sym
      (step s(signed s n) + x) 🝖[ _≡_ ]-[ congruence₂ₗ(_+_)(x) (𝐒-to-step{s}{n}) ]-sym
      (signed s (ℕ.𝐒 n) + x)   🝖-end
    {-# INLINE ps #-}

    p {signed s₁ ℕ.𝟎}      {signed s₂ ℕ.𝟎}      = congruence₂(_+_) (𝟎-signs {s₁}{s₂}) (𝟎-signs {s₂}{s₁})
    p {signed s₁ ℕ.𝟎}      {signed s₂ (ℕ.𝐒 n₂)} = ps {signed s₁ ℕ.𝟎}{s₂}{n₂}
    p {signed s₁ (ℕ.𝐒 n₁)} {signed s₂ ℕ.𝟎}      = symmetry(_≡_) (ps {signed s₂ ℕ.𝟎}{s₁}{n₁})
    p {signed s₁ (ℕ.𝐒 n₁)} {signed s₂ (ℕ.𝐒 n₂)} = ps {signed s₁ (ℕ.𝐒 n₁)}{s₂}{n₂}
    p {signed ➕ ℕ.𝟎}     {𝟎-sign i}          j = 𝟎-sign (Interval.max i (Interval.flip j))
    p {signed ➖ ℕ.𝟎}     {𝟎-sign i}          j = 𝟎-sign (Interval.min i j)
    p {signed ➕ (ℕ.𝐒 n)} {𝟎-sign i}          j = {!!}
    p {signed ➖ (ℕ.𝐒 n)} {𝟎-sign i}          j = {!!}
    p {𝟎-sign i}          {signed ➕ ℕ.𝟎}     j = 𝟎-sign (Interval.max i j)
    p {𝟎-sign i}          {signed ➖ ℕ.𝟎}     j = 𝟎-sign (Interval.min i (Interval.flip j))
    p {𝟎-sign i}          {signed ➕ (ℕ.𝐒 n)} j = {!!}
    p {𝟎-sign i}          {signed ➖ (ℕ.𝐒 n)} j = {!!}
    p {𝟎-sign i}          {𝟎-sign j}         k = {!!}

instance
  [+]-identityᵣ : Identityᵣ(_+_)(𝟎)
  Identityᵣ.proof [+]-identityᵣ {signed _ _} = reflexivity(_≡_)
  Identityᵣ.proof [+]-identityᵣ {𝟎-sign i} = reflexivity(_≡_)

instance
  [+]-identityₗ : Identityₗ(_+_)(𝟎)
  Identityₗ.proof [+]-identityₗ {x} = commutativity(_+_) {𝟎}{x} 🝖 identityᵣ(_+_)(𝟎)

open import Logic.IntroInstances

instance
  [+][−]-inverseFunctionᵣ : InverseFunctionᵣ(_+_)(−_)
  [+][−]-inverseFunctionᵣ = intro(\{x} → p{x}) where
    p : Names.InverseFunctionᵣ(_+_)(𝟎)(−_)
    p {signed ➕ ℕ.𝟎} = reflexivity(_≡_)
    p {signed ➖ ℕ.𝟎} = 𝟎-sign
    p {signed s (ℕ.𝐒 n)} =
      signed s (ℕ.𝐒 n) + (− signed s (ℕ.𝐒 n))                     🝖[ _≡_ ]-[]
      signed s (ℕ.𝐒 n) + signed (Sign.− s) (ℕ.𝐒 n)                🝖[ _≡_ ]-[ congruence₂(_+_) (𝐒-to-step {s} {n}) (𝐒-to-step {Sign.− s} {n}) ]
      step s (signed s n) + step (Sign.− s) (signed (Sign.− s) n) 🝖[ _≡_ ]-[ [+]ₗ-of-step {s}{signed s n}{step (Sign.− s) (signed (Sign.− s) n)} ]
      step s (signed s n + step (Sign.− s) (signed (Sign.− s) n)) 🝖[ _≡_ ]-[ congruence₂ᵣ(step)(s) ([+]ᵣ-of-step {Sign.− s}{signed s n}{signed (Sign.− s) n}) ]
      step s (step (Sign.− s) (signed s n + signed (Sign.− s) n)) 🝖[ _≡_ ]-[ step-inverses (Sign.[−]-no-fixpoints ∘ symmetry(Id)) ]
      signed s n + signed (Sign.− s) n                            🝖[ _≡_ ]-[]
      signed s n + (− signed s n)                                 🝖[ _≡_ ]-[ p{signed s n} ]
      𝟎                                                           🝖-end
    p {𝟎-sign i} j = {!!}

instance
  [+]-associativity : Associativity(_+_)
  [+]-associativity = intro(\{x}{y}{z} → p{x}{y}{z}) where
    p : Names.Associativity(_+_)
    p {x} {y} {signed s ℕ.𝟎} = reflexivity(_≡_)
    p {x} {y} {signed s (ℕ.𝐒 z)} =
      (x + y) + signed s (ℕ.𝐒 z)    🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x + y) (𝐒-to-step {s}{z}) ]
      (x + y) + step s (signed s z) 🝖[ _≡_ ]-[ [+]ᵣ-of-step {s}{x + y}{signed s z} ]
      step s ((x + y) + signed s z) 🝖[ _≡_ ]-[ congruence₂ᵣ(step)(s) (p{x}{y}{signed s z}) ]
      step s (x + (y + signed s z)) 🝖[ _≡_ ]-[ [+]ᵣ-of-step {s}{x}{y + signed s z} ]-sym
      x + step s (y + signed s z)   🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x) ([+]ᵣ-of-step {s}{y}{signed s z}) ]-sym
      x + (y + step s (signed s z)) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x) (congruence₂ᵣ(_+_)(y) (𝐒-to-step {s})) ]-sym
      x + (y + signed s (ℕ.𝐒 z))    🝖-end
    p {x} {y} {𝟎-sign i} = reflexivity(_≡_)

Stepᵣ-injective : ∀{s}{x y} → (step s x ≡ step s y) → (x ≡ y)
Stepᵣ-injective {s} {x} {y} p = symmetry(_≡_) (step-inverses Sign.[−]-no-fixpoints) 🝖 congruence₂ᵣ(step)(Sign.− s) p 🝖 step-inverses Sign.[−]-no-fixpoints

ℕ-Path-to-Id : ∀{x y : ℕ} → (Path x y) → (Id x y)
ℕ-Path-to-Id {ℕ.𝟎} {ℕ.𝟎} p = Id-intro
ℕ-Path-to-Id {ℕ.𝟎} {ℕ.𝐒 y} p = {!!}
ℕ-Path-to-Id {ℕ.𝐒 x} {ℕ.𝟎} p = {!!}
ℕ-Path-to-Id {ℕ.𝐒 x} {ℕ.𝐒 y} p = {!ℕ-Path-to-Id {x}{y}!}

Signedᵣ-injective : ∀{s}{x y} → (signed s x ≡ signed s y) → (Id x y)
Signedᵣ-injective {s} {ℕ.𝟎}   {ℕ.𝟎}   p = Id-intro
Signedᵣ-injective {s} {ℕ.𝟎}   {ℕ.𝐒 y} p = {!!}
Signedᵣ-injective {s} {ℕ.𝐒 x} {ℕ.𝟎}   p = {!!}
Signedᵣ-injective {s} {ℕ.𝐒 x} {ℕ.𝐒 y} p = congruence₁ ⦃ Id-equiv ⦄ ⦃ Id-equiv ⦄ (ℕ.𝐒) ⦃ Id-function ⦄ (Signedᵣ-injective (Stepᵣ-injective(symmetry(_≡_) 𝐒-to-step 🝖 p 🝖 𝐒-to-step)))

ℤ-different-identities : ¬(𝟎 ≡ 𝟏)
ℤ-different-identities p with () ← Signedᵣ-injective p
