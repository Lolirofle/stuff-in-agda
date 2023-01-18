{-# OPTIONS --cubical #-}

module Miscellaneous.CubicalInteger where

import      Lvl
open import Numeral.Natural as ℕ using (ℕ)
open import Numeral.Charge as Charge using (Charge ; ➖ ; ➕)
open import Numeral.Sign as Sign using (Sign ; ➖ ; ➕)
import      Numeral.Sign.Oper as Sign
open import Type.Cubical
open import Type.Cubical.Path
open import Type.Cubical.Path.Equality
open import Type

--apply : ∀{ℓ}{T : Type{ℓ}}{x y : T} → Interval → (x ≡ y) → T
-- apply i xy = xy i

infix 10010 −ₙ_ +ₙ_
infix 10020 _+_ _−_

-- The type of integers ℤ = {…,−2,−1,0,1,2,…}.
-- Represented by using the exclusive union of ℕ and ℕ, but the zeroes are equal.
data ℤ : Type{Lvl.𝟎} where
  signed : Sign → ℕ → ℤ
  𝟎-sign : Path(signed ➖ ℕ.𝟎) (signed ➕ ℕ.𝟎)

-- Intuitive constructor patterns
-- −ₙ_ : ℕ → ℤ
-- +ₙ_ : ℕ → ℤ
pattern −ₙ_ n = signed ➖ n
pattern +ₙ_ n = signed ➕ n
pattern 𝟎  = +ₙ(ℕ.𝟎) -- Zero (0).
pattern 𝟏  = +ₙ(ℕ.𝟏) -- One (1).
pattern −𝟏 = −ₙ(ℕ.𝟏) -- Negative one (−1).

-- open import Structure.Relator.Properties
open import Type.Cubical.Path.Functions

elim : ∀{ℓ} → (P : ℤ → Type{ℓ}) → (neg : (n : ℕ) → P(−ₙ n)) → (pos : (n : ℕ) → P(+ₙ n)) → PathP(map P 𝟎-sign $ₚₐₜₕ_) (neg ℕ.𝟎) (pos ℕ.𝟎) → ((n : ℤ) → P(n))
elim(P) neg _   eq (−ₙ n) = neg n
elim(P) _   pos eq (+ₙ n) = pos n
elim(P) _   _   eq (𝟎-sign i) = eq i

rec : ∀{ℓ}{T : Type{ℓ}} → (neg : ℕ → T) → (pos : ℕ → T) → Path (neg ℕ.𝟎) (pos ℕ.𝟎) → ((n : ℤ) → T)
rec = elim _

-- Sign.
-- The sign part of an integer where zero is interpreted as positive.
-- Notes on the proof of the path:
--   The 𝟎-sign case guarantees that the function respects the congruence property (in this case (−0 = +0) → (sign(−0) = sign(+0))).
--   It is proven by providing the value on a path varying on the variable `i`. In this case, it is constant (both −0 and +0 maps to ➕).
sign : ℤ → Sign
sign (signed _ ℕ.𝟎)      = ➕
sign (signed s (ℕ.𝐒(_))) = s
sign (𝟎-sign i) = ➕

-- Zeroable sign.
sign₀ : ℤ → Charge
sign₀ (signed s ℕ.𝟎)      = Charge.𝟎
sign₀ (signed s (ℕ.𝐒(_))) = Sign.zeroable s
sign₀ (𝟎-sign i) = Charge.𝟎

-- Absolute value.
-- The natural part of an integer.
absₙ : ℤ → ℕ
absₙ(signed _ n) = n
absₙ(𝟎-sign _) = ℕ.𝟎

-- TODO: MereProposition(A) → MereProposition(B) → ((A ↔ B) ≡ (A ≡ B))
-- TODO: Above should be used in the proof of elimProp. It should be possible to prove by using the univalence axiom and the fact that (_↔_) should be an isomorphism for mere propositions?

open import Logic.Propositional
open import Type.Properties.MereProposition
open import Type.Cubical.Path.Proofs
elimProp : ∀{ℓ} → (P : ℤ → Type{ℓ}) ⦃ prop : ∀{x} → MereProposition(P(x)) ⦄ → (neg : (n : ℕ) → P(−ₙ n)) → (pos : (n : ℕ) → P(+ₙ n)) → ((n : ℤ) → P(n))
elimProp P neg pos = elim(P) neg pos (interval-predicate₁-path{Y = P} 𝟎-sign)

open import Data
open import Structure.Type.Identity
open import Structure.Relator.Properties
open import Type.Properties.Homotopy

open import Data.Boolean
test : Sign → Sign → Bool
test ➕ ➕ = 𝑇
test ➕ ➖ = 𝐹
test ➖ ➕ = 𝐹
test ➖ ➖ = 𝑇
-- if test x y then P xy else Empty

open import Type.Identity
open import Type.Identity.Proofs

test10 : ∀{x y : Sign} → Id x y → Path x y
test10 {x} {.x} intro = point

test11 : ∀{x y : Sign} → Path x y → Id x y
test11 {➕} {➕} p = intro
test11 {➕} {➖} p = {!!}
test11 {➖} {➕} p = {!!}
test11 {➖} {➖} p = intro

test12 : ∀{x y}{p : Path x y} → Path (test10(test11 p)) p
test12 {➕} {➕}{p} i j = {!!}
test12 {➕} {➖} = {!!}
test12 {➖} {➕} = {!!}
test12 {➖} {➖} = {!!}

test13 : ∀{x y}{p : Id x y} → Path (test11(test10 p)) p
test13 {➕} {p = intro} i = intro
test13 {➖} {p = intro} i = intro

open import Functional
open import Structure.Type.Identity.Proofs

instance
  Sign-Id-kElim : ∀{ℓₚ} → IdentityKEliminator(Id{T = Sign}) {ℓₚ}
  IdentityKEliminator.elim Sign-Id-kElim P p x@{➕} = idElimFixedᵣ(Id) (\{y} → Sign.elim{P = \y → Id x y → Type} (const Empty) P y) p
  IdentityKEliminator.elim Sign-Id-kElim P p x@{➖} = idElimFixedᵣ(Id) (\{y} → Sign.elim{P = \y → Id x y → Type} P (const Empty) y) p

instance
  Sign-kElim : ∀{ℓₚ} → IdentityKEliminator(Path{P = Sign}) {ℓₚ}
  IdentityKEliminator.elim Sign-kElim P p x@{➕} = idElimFixedᵣ(Path) (\{y} → Sign.elim{P = \y → Path x y → Type} (const Empty) P y) p
  IdentityKEliminator.elim Sign-kElim P p x@{➖} = idElimFixedᵣ(Path) (\{y} → Sign.elim{P = \y → Path x y → Type} P (const Empty) y) p

instance
  Sign-uip : UniqueIdentityProofs(Sign)
  Sign-uip = idKElim-to-uip(Sign)

Sign-set : HomotopyLevel 2 Sign
Sign-set = intro(\{x}{y} → uniqueness(Path x y))

open import Logic.Propositional.Equiv
open import Numeral.Natural.Induction
open import Structure.Relator

instance
  ℕ-Id-kElim : ∀{ℓₚ} → IdentityKEliminator(Id{T = ℕ}) {ℓₚ}
  IdentityKEliminator.elim ℕ-Id-kElim P p {ℕ.𝟎} intro = p
  IdentityKEliminator.elim ℕ-Id-kElim P p {ℕ.𝐒 x} eq = {!idElimFixedᵣ(Id) {x = ℕ.𝐒 x} (\{y} xy → P{y} (substitute₂-₁ᵣ ⦃ Id-equiv ⦄ ⦃ Id-equiv ⦄ (Id) ⦃ Id-to-function₂ ⦄ (y) {ℕ.𝐒 x}{y} xy xy)) {!p!} {ℕ.𝐒 x} eq!}
  -- idElimFixedᵣ(Id) {x = ℕ.𝐒 x} (\{y} xy → P{y} (substitute₂-₁ᵣ ⦃ Id-equiv ⦄ ⦃ Id-equiv ⦄ (Id) ⦃ Id-to-function₂ ⦄ (y) {ℕ.𝐒 x}{y} xy xy)) {!p!} {ℕ.𝐒 x} eq
  -- idElimFixedᵣ(Id) (\{y} → ℕ-elim(\y → Id x y → Type) (const Empty) (\a b → {!P!}) y) {!!} {!!}

ℕ-set : HomotopyLevel 2 ℕ
HomotopyLevel.proof ℕ-set = {!!}

ℤ-set : HomotopyLevel 2 ℤ
HomotopyLevel.proof ℤ-set {x}{y} {p}{q} = {!x y!}

-- elimSet : ∀{ℓ} → (P : ℤ → Type{ℓ}) ⦃ set : ∀{x} → HomotopyLevel 2 (P(x)) ⦄ → (neg : (n : ℕ) → P(−ₙ n)) → (pos : (n : ℕ) → P(+ₙ n)) → (P(−ₙ ℕ.𝟎) ↔ P(+ₙ ℕ.𝟎)) → ((n : ℤ) → P(n))
-- elimSet P neg pos z = elim(P) neg pos {!!}

{-

open import Data.Either
open import Functional using (_$_)
import      Numeral.Sign.Oper as Sign
import      Numeral.Natural.Oper as ℕ
open import Relator.Equals using () renaming (_≡_ to Id ; [≡]-intro to Id-intro)
open import Relator.Equals.Proofs.Equivalence using () renaming ([≡]-equiv to Id-equiv ; [≡]-symmetry to Id-symmetry ; [≡]-to-function to Id-to-function ; [≡]-function to Id-function)
open import Syntax.Transitivity

Sign-decidable-eq : ∀(s₁ s₂ : Sign) → ((Id s₁ s₂) ∨ ¬(Id s₁ s₂))
Sign-decidable-eq ➕ ➕ = [∨]-introₗ Id-intro
Sign-decidable-eq ➕ ➖ = [∨]-introᵣ \()
Sign-decidable-eq ➖ ➕ = [∨]-introᵣ \()
Sign-decidable-eq ➖ ➖ = [∨]-introₗ Id-intro

step : Sign → ℤ → ℤ
step s₁ (signed s₂ n) with Sign-decidable-eq s₁ s₂
step _  (signed s n)         | Left  _ = signed s (ℕ.𝐒(n))
step s₁ (signed s₂ ℕ.𝟎)      | Right _ = signed s₁ (ℕ.𝐒(ℕ.𝟎))
step s₁ (signed s₂ (ℕ.𝐒(n))) | Right _ = signed s₂ n
step ➕ (𝟎-sign i) = 𝟏
step ➖ (𝟎-sign i) = −𝟏

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
abs(𝟎-sign i) = 𝟎

-- Addition.
_+_ : ℤ → ℤ → ℤ
x + (signed _ ℕ.𝟎)      = x
x + (signed s (ℕ.𝐒(y))) = step s (x + (signed s y))
x + 𝟎-sign i = x

-- Subtraction.
_−_ : ℤ → ℤ → ℤ
x − y = x + (− y)

import Numeral.Natural.Oper.Proofs as ℕ

_⋅_ : ℤ → ℤ → ℤ
x ⋅ y = signed ((sign x) Sign.⨯ (sign y)) ((absₙ x) ℕ.⋅ (absₙ y))

open import Data.Boolean
open import Data.Boolean.Stmt
import      Numeral.Natural.Oper.Comparisons as ℕ
nonZero : ℤ → Bool 
nonZero = ℕ.positive? Functional.∘ absₙ

NonZero : ℤ → Type
NonZero = IsTrue Functional.∘ nonZero

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
  step s₂ (step s₁ x + signed s₂ n)   🝖[ _≡_ ]-[ congruence₂-₂(step)(s₂) ([+]ₗ-of-step {s₁} {x} {signed s₂ n}) ]
  step s₂ (step s₁ (x + signed s₂ n)) 🝖[ _≡_ ]-[ step-swap{s₂}{s₁}{x + signed s₂ n} ]
  step s₁ (step s₂ (x + signed s₂ n)) 🝖[ _≡_ ]-[ congruence₂-₂(step)(s₁) ([+]ᵣ-of-step {s₂} {x} {signed s₂ n}) ]-sym
  step s₁ (x + step s₂ (signed s₂ n)) 🝖[ _≡_ ]-[ congruence₂-₂(step)(s₁) (congruence₂-₂(_+_)(x) (𝐒-to-step {s₂}{n})) ]-sym
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
      (x + signed s (ℕ.𝐒 n))   🝖[ _≡_ ]-[ congruence₂-₂(_+_)(_) (𝐒-to-step{s}{n}) ]
      (x + step s(signed s n)) 🝖[ _≡_ ]-[ [+]ᵣ-of-step {s}{x}{signed s n} ]
      step s(x + signed s n)   🝖[ _≡_ ]-[ congruence₂-₂(step)(s) (p {x} {signed s n}) ]
      step s(signed s n + x)   🝖[ _≡_ ]-[ [+]ₗ-of-step {s}{signed s n}{x} ]-sym
      (step s(signed s n) + x) 🝖[ _≡_ ]-[ congruence₂-₁(_+_)(x) (𝐒-to-step{s}{n}) ]-sym
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
    p {𝟎-sign i}          {𝟎-sign j}          k = {!!}

instance
  [+]-identityᵣ : Identityᵣ(_+_)(𝟎)
  Identityᵣ.proof [+]-identityᵣ {signed _ _} = reflexivity(_≡_)
  Identityᵣ.proof [+]-identityᵣ {𝟎-sign i} = reflexivity(_≡_)

instance
  [+]-identityₗ : Identityₗ(_+_)(𝟎)
  Identityₗ.proof [+]-identityₗ {x} = commutativity(_+_) {𝟎}{x} 🝖 identityᵣ(_+_)(𝟎)

instance
  [+]-identity : Identity(_+_)(𝟎)
  [+]-identity = intro

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
      step s (signed s n + step (Sign.− s) (signed (Sign.− s) n)) 🝖[ _≡_ ]-[ congruence₂-₂(step)(s) ([+]ᵣ-of-step {Sign.− s}{signed s n}{signed (Sign.− s) n}) ]
      step s (step (Sign.− s) (signed s n + signed (Sign.− s) n)) 🝖[ _≡_ ]-[ step-inverses (Sign.[−]-no-fixpoints ∘ symmetry(Id)) ]
      signed s n + signed (Sign.− s) n                            🝖[ _≡_ ]-[]
      signed s n + (− signed s n)                                 🝖[ _≡_ ]-[ p{signed s n} ]
      𝟎                                                           🝖-end
    p {𝟎-sign i} j = 𝟎-sign (Interval.max i j)

instance
  [+][−]-inverseFunctionₗ : InverseFunctionₗ(_+_)(−_)
  InverseFunctionₗ.proof [+][−]-inverseFunctionₗ {x} = commutativity(_+_) {− x}{x} 🝖 inverseFunctionᵣ(_+_)(−_) {x}

instance
  [+][−]-inverseFunction : InverseFunction(_+_)(−_)
  [+][−]-inverseFunction = intro

instance
  [+]-associativity : Associativity(_+_)
  [+]-associativity = intro(\{x}{y}{z} → p{x}{y}{z}) where
    p : Names.Associativity(_+_)
    p {x} {y} {signed s ℕ.𝟎} = reflexivity(_≡_)
    p {x} {y} {signed s (ℕ.𝐒 z)} =
      (x + y) + signed s (ℕ.𝐒 z)    🝖[ _≡_ ]-[ congruence₂-₂(_+_)(x + y) (𝐒-to-step {s}{z}) ]
      (x + y) + step s (signed s z) 🝖[ _≡_ ]-[ [+]ᵣ-of-step {s}{x + y}{signed s z} ]
      step s ((x + y) + signed s z) 🝖[ _≡_ ]-[ congruence₂-₂(step)(s) (p{x}{y}{signed s z}) ]
      step s (x + (y + signed s z)) 🝖[ _≡_ ]-[ [+]ᵣ-of-step {s}{x}{y + signed s z} ]-sym
      x + step s (y + signed s z)   🝖[ _≡_ ]-[ congruence₂-₂(_+_)(x) ([+]ᵣ-of-step {s}{y}{signed s z}) ]-sym
      x + (y + step s (signed s z)) 🝖[ _≡_ ]-[ congruence₂-₂(_+_)(x) (congruence₂-₂(_+_)(y) (𝐒-to-step {s})) ]-sym
      x + (y + signed s (ℕ.𝐒 z))    🝖-end
    p {x} {y} {𝟎-sign i} = reflexivity(_≡_)

open import Structure.Operator.Proofs
instance
  [+]-cancellationₗ : Cancellationₗ(_+_)
  [+]-cancellationₗ = One.cancellationₗ-by-associativity-inverse {_▫_ = _+_}

instance
  [+]-cancellationᵣ : Cancellationᵣ(_+_)
  [+]-cancellationᵣ = One.cancellationᵣ-by-associativity-inverse {_▫_ = _+_}

Stepᵣ-injective : ∀{s}{x y} → (step s x ≡ step s y) → (x ≡ y)
Stepᵣ-injective {s} {x} {y} p = symmetry(_≡_) (step-inverses Sign.[−]-no-fixpoints) 🝖 congruence₂-₂(step)(Sign.− s) p 🝖 step-inverses Sign.[−]-no-fixpoints

open import Numeral.Natural.Equiv.Path

instance
  absₙ-signed-inverses : ∀{s} → Inverseᵣ(absₙ)(signed s)
  Inverseᵣ.proof (absₙ-signed-inverses {➕}) = reflexivity(Path)
  Inverseᵣ.proof (absₙ-signed-inverses {➖}) = reflexivity(Path)

Signedᵣ-injective : ∀{s}{x y} → (signed s x ≡ signed s y) → (Id x y)
Signedᵣ-injective {s} p = sub₂(_≡_)(Id) (symmetry(Path) (inverseᵣ(absₙ)(signed s)) 🝖 congruence₁(absₙ) p 🝖 inverseᵣ(absₙ)(signed s))

ℤ-different-identities : ¬(𝟎 ≡ 𝟏)
ℤ-different-identities p with () ← Signedᵣ-injective p

open import Structure.Relator

instance
  postulate [⋅]-commutativity : Commutativity(_⋅_)
  {-Commutativity.proof [⋅]-commutativity {signed s₁ x} {signed s₂ y} = congruence₂(signed) (sub₂(Id)(Path) (commutativity ⦃ Id-equiv ⦄ (Sign._⨯_) {s₁}{s₂})) (sub₂(Id)(Path) (commutativity ⦃ Id-equiv ⦄ (ℕ._⋅_) {x}{y}))
  Commutativity.proof [⋅]-commutativity {signed ➕ x} {𝟎-sign i} j    = {!!}
  -- {!substitute₁ᵣ(\expr → ((signed ➕ x) ⋅ expr) ≡ (expr ⋅ (signed ➕ x))) ? ?!}
  Commutativity.proof [⋅]-commutativity {signed ➖ x} {𝟎-sign i}    = {!sub₂(Id)(Path) ?!}
  Commutativity.proof [⋅]-commutativity {𝟎-sign i}    {signed s y}  = {!𝟎-sign i!}
  Commutativity.proof [⋅]-commutativity {𝟎-sign i}    {𝟎-sign i₁}   = {!!}-}
  {-Commutativity.proof [⋅]-commutativity {signed s₁ x} {signed s₂ y}
    rewrite commutativity ⦃ Id-equiv ⦄ (ℕ._⋅_) {x}{y}
    rewrite commutativity ⦃ Id-equiv ⦄ (Sign._⨯_) {s₁}{s₂}
    = reflexivity(Path)
  Commutativity.proof [⋅]-commutativity {signed ➕ x} {𝟎-sign i}    = {!substitute₁ᵣ(\expr → ((signed ➕ x) ⋅ expr) ≡ (expr ⋅ (signed ➕ x))) ? ?!}
  Commutativity.proof [⋅]-commutativity {signed ➖ x} {𝟎-sign i}    = {!sub₂(Id)(Path) ?!}
  Commutativity.proof [⋅]-commutativity {𝟎-sign i}    {signed s y}  = {!𝟎-sign i!}
  Commutativity.proof [⋅]-commutativity {𝟎-sign i}    {𝟎-sign i₁}   = {!!}-}
-- (signed ➕ x) ⋅ -0 ≡ -0 ⋅ (signed ➕ x)
-- (signed ➕ x) ⋅ +0 ≡ +0 ⋅ (signed ➕ x)

open import Numeral.Sign.Proofs
open import Structure.Operator

absₙ-of-signed : ∀{s x} → Id (absₙ(signed s x)) x
absₙ-of-signed {➕} = reflexivity(Id)
absₙ-of-signed {➖} = reflexivity(Id)

signed-inverse : ∀{x} → (signed(sign x) (absₙ x) ≡ x)
signed-inverse {signed ➕ ℕ.𝟎}     = reflexivity(Path)
signed-inverse {signed ➕ (ℕ.𝐒 n)} = reflexivity(Path)
signed-inverse {signed ➖ ℕ.𝟎}     = symmetry(Path) 𝟎-sign
signed-inverse {signed ➖ (ℕ.𝐒 n)} = reflexivity(Path)
signed-inverse {𝟎-sign i} j = 𝟎-sign (Interval.max i (Interval.flip j))

instance
  postulate [⋅]-associativity : Associativity(_⋅_)
  -- Associativity.proof [⋅]-associativity {x} {y} {z} = {!(x ⋅ y) ⋅ z!}

instance
  [⋅]-identityᵣ : Identityᵣ(_⋅_)(𝟏)
  Identityᵣ.proof [⋅]-identityᵣ {x} rewrite identityᵣ(Sign._⨯_)(➕) {sign(x)} = signed-inverse

instance
  [⋅]-identityₗ : Identityₗ(_⋅_)(𝟏)
  Identityₗ.proof [⋅]-identityₗ {x} rewrite identityₗ(Sign._⨯_)(➕) {sign(x)} = signed-inverse

instance
  [⋅]-identity : Identity(_⋅_)(𝟏)
  [⋅]-identity = intro

instance
  postulate [⋅][+]-distributivityₗ : Distributivityₗ(_⋅_)(_+_)

instance
  postulate [⋅][+]-distributivityᵣ : Distributivityᵣ(_⋅_)(_+_)

open import Logic.Predicate
open import Structure.Operator.Field
open import Structure.Operator.Group
open import Structure.Operator.Monoid
open import Structure.Operator.Ring

instance
  [+]-monoid : Monoid(_+_)
  Monoid.identity-existence [+]-monoid = [∃]-intro 𝟎

instance
  [+]-group : Group(_+_)
  [+]-group = Group-from-monoid(_+_)(−_)

instance
  [+]-commutativeGroup : CommutativeGroup(_+_)
  [+]-commutativeGroup = intro

instance
  [⋅]-monoid : Monoid(_⋅_)
  Monoid.identity-existence [⋅]-monoid = [∃]-intro 𝟏
open Monoid([⋅]-monoid) using() renaming(semi to [⋅]-semi)

instance
  [⋅]-distributivity : Distributivity(_⋅_)(_+_)
  [⋅]-distributivity = intro

open import Logic.Propositional.Theorems
import      Numeral.Natural.Oper.Proofs.Structure as ℕ
import      Structure.Function.Names as Names

instance
  absₙ-function : Function ⦃ Path-equiv ⦄ ⦃ Id-equiv ⦄ (absₙ)
  Function.congruence absₙ-function xy = sub₂(Path)(Id) (congruence₁(absₙ) xy)

absₙ-injective-for-0 : ∀{x} → Id(absₙ(x)) ℕ.𝟎 → (x ≡ 𝟎)
absₙ-injective-for-0 {x} eq =
  x                        🝖[ _≡_ ]-[ signed-inverse{x} ]-sym
  signed (sign x) (absₙ x) 🝖[ _≡_ ]-[ congruence₂-₂(signed)(sign x) (sub₂(Id)(Path) eq) ]
  signed (sign x) ℕ.𝟎      🝖[ _≡_ ]-[ 𝟎-signs ]
  signed ➕ ℕ.𝟎            🝖-end

instance
  ℤ-nonZeroRelation : NonIdentityRelation([+]-monoid)
  NonIdentityRelation.NonIdentity ℤ-nonZeroRelation = NonZero
  NonIdentityRelation.proof ℤ-nonZeroRelation {x} = [↔]-transitivity
    (NonIdentityRelation.proof ⦃ _ ⦄ ℕ.ℕ-nonZero {absₙ x})
    ([↔]-intro
      (contrapositiveᵣ absₙ-injective-for-0)
      (contrapositiveᵣ(congruence₁ ⦃ Path-equiv ⦄ ⦃ Id-equiv ⦄ (absₙ)))
    )

instance
  [⋅]-ring : Ring(_+_)(_⋅_)
  [⋅]-ring = intro
open Ring([⋅]-ring) using()
  renaming(
    unity to [⋅]-unity ;
    rg    to [⋅]-rg ;
    rng   to [⋅]-rng
  )

instance
  [⋅]-ringNonZero : Unity.DistinctIdentities [⋅]-unity
  [⋅]-ringNonZero = record {}
  -- Ring.NonZero.proof [⋅]-ringNonZero = ℤ-different-identities ∘ symmetry(_≡_)

open import Data
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Boolean.Stmt
open import Functional
import      Numeral.Natural.Oper.Comparisons as ℕ
import      Numeral.Natural.Oper.Comparisons.Proofs as ℕ

test : Sign → Sign → (ℕ → ℕ → Bool)
test ➕ ➕ = (ℕ._≤?_)
test ➕ ➖ = ((_&&_) on₂ ((!) ∘ ℕ.positive?))
test ➖ ➕ = (const ∘ const) 𝑇
test ➖ ➖ = (ℕ._≥?_)

_≤?_ : ℤ → ℤ → Bool
signed s₁ x ≤? signed s₂ y = test s₁ s₂ x y
signed ➕ ℕ.𝟎     ≤? 𝟎-sign _ = 𝑇
signed ➕ (ℕ.𝐒 x) ≤? 𝟎-sign _ = 𝐹
signed ➖ _       ≤? 𝟎-sign _ = 𝑇
𝟎-sign _ ≤? signed ➕ _       = 𝑇
𝟎-sign _ ≤? signed ➖ ℕ.𝟎     = 𝑇
𝟎-sign _ ≤? signed ➖ (ℕ.𝐒 y) = 𝐹
𝟎-sign _ ≤? 𝟎-sign _ = 𝑇

_≤_ : ℤ → ℤ → Type{Lvl.𝟎}
_≤_ = IsTrue ∘₂ (_≤?_)

{-data _≤_ : ℤ → ℤ → Type{Lvl.𝟎} where
  neg : ∀{x y} → (x ℕ.≥ y) → ((signed ➖ x) ≤ (signed ➖ y))
  mix : ∀{x y} → ((signed ➖ x) ≤ (signed ➕ y))
  pos : ∀{x y} → (x ℕ.≤ y) → ((signed ➕ x) ≤ (signed ➕ y))
-}

instance
  [≤]-reflexivity : Reflexivity(_≤_)
  Reflexivity.proof [≤]-reflexivity {signed ➕ ℕ.𝟎} = <>
  Reflexivity.proof [≤]-reflexivity {signed ➕ (ℕ.𝐒 x)} = ℕ.[≤?]-reflexivity {x}
  Reflexivity.proof [≤]-reflexivity {signed ➖ ℕ.𝟎} = <>
  Reflexivity.proof [≤]-reflexivity {signed ➖ (ℕ.𝐒 x)} = ℕ.[≤?]-reflexivity {x}
  Reflexivity.proof [≤]-reflexivity {𝟎-sign i} = <>

{-
instance
  [≤]-antisymmetry : Antisymmetry(_≤_)(_≡_)
  Antisymmetry.proof [≤]-antisymmetry {signed x x₁} {signed x₂ x₃} lt gt = ?
  Antisymmetry.proof [≤]-antisymmetry {signed x x₁} {𝟎-sign i} lt gt = ?
  Antisymmetry.proof [≤]-antisymmetry {𝟎-sign i} {signed x x₁} lt gt = ?
  Antisymmetry.proof [≤]-antisymmetry {𝟎-sign i} {𝟎-sign i₁} lt gt = ?
-}
-}
