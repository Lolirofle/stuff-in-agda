module Numeral.Natural.Relation.Divisibility.Two where

open import Data
import      Lvl
open import Numeral.Finite
open import Numeral.Natural as ℕ
open import Numeral.Natural.Relation.DivisibilityWithRemainder
open import Syntax.Number
open import Type

-- Alternative definition:
--   data Even : ℕ → Type{Lvl.𝟎} where
--     base : Even(ℕ.𝟎)
--     step : ∀{n} → Even(n) → Even(ℕ.𝐒(ℕ.𝐒(n)))
Even : ℕ → Type
Even n = (2 ∣ᵣₑₘ n)(0)

-- Alternative definition:
--   data Odd : ℕ → Type{Lvl.𝟎} where
--     base : Odd(ℕ.𝟏)
--     step : ∀{n} → Odd(n) → Odd(ℕ.𝐒(ℕ.𝐒(n)))
Odd : ℕ → Type
Odd n = (2 ∣ᵣₑₘ n)(1)

open import Functional
open import Logic.Propositional
open import Numeral.Natural.Oper.Proofs.Rewrite
open import Numeral.Natural.Relation.Divisibility

private variable n : ℕ

div-even : Even(n) ↔ (2 ∣ n)
div-even = [↔]-intro l r where
  l : Even(n) ← (2 ∣ n)
  l Div𝟎     = DivRem𝟎
  l (Div𝐒 p) = DivRem𝐒 (l p)

  r : Even(n) → (2 ∣ n)
  r DivRem𝟎     = Div𝟎
  r (DivRem𝐒 p) = Div𝐒 (r p)

div-odd : Odd(n) ↔ (2 ∤ n)
div-odd = [↔]-intro l r where
  l : Odd(n) ← (2 ∤ n)
  l {𝟎} ndiv = [⊥]-elim (ndiv Div𝟎)
  l {𝐒 𝟎} ndiv = DivRem𝟎
  l {𝐒 (𝐒 n)} ndiv = DivRem𝐒(l(ndiv ∘ Div𝐒))

  r : Odd(n) → (2 ∤ n)
  r DivRem𝟎 ()
  r (DivRem𝐒 odd) (Div𝐒 div) = r odd div

even-or-odd : Even(n) ∨ Odd(n)
even-or-odd {ℕ.𝟎}         = [∨]-introₗ DivRem𝟎
even-or-odd {ℕ.𝟏}         = [∨]-introᵣ DivRem𝟎
even-or-odd {ℕ.𝐒(ℕ.𝐒(n))} = [∨]-elim ([∨]-introₗ ∘ DivRem𝐒) ([∨]-introᵣ ∘ DivRem𝐒) (even-or-odd{n})

open import Logic.Predicate
open import Numeral.Natural.Oper
open import Numeral.Natural.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function.Domain

-- Note: Special case of [∣ᵣₑₘ]-equivalence.
even-existence : Even(n) ↔ ∃(k ↦ k ⋅ 2 ≡ n)
even-existence = [↔]-intro l r where
  l : Even(n) ← ∃(k ↦ k ⋅ 2 ≡ n)
  l {ℕ.𝟎}         ([∃]-intro _        ⦃ p ⦄) = DivRem𝟎
  l {ℕ.𝐒(ℕ.𝐒(n))} ([∃]-intro (ℕ.𝐒(k)) ⦃ p ⦄) = DivRem𝐒 (l{n} ([∃]-intro k ⦃ injective(ℕ.𝐒) (injective(ℕ.𝐒) p) ⦄))

  r : Even(n) → ∃(k ↦ k ⋅ 2 ≡ n)
  r DivRem𝟎 = [∃]-intro 0
  r (DivRem𝐒 en) with [∃]-intro k ⦃ [≡]-intro ⦄ ← r en = [∃]-intro (𝐒(k))

-- Note: Special case of [∣ᵣₑₘ]-equivalence.
odd-existence : Odd(n) ↔ ∃(k ↦ (k ⋅ 2) + 1 ≡ n)
odd-existence = [↔]-intro l r where
  l : Odd(n) ← ∃(k ↦ (k ⋅ 2) + 1 ≡ n)
  l {ℕ.𝟏}         ([∃]-intro _     ⦃ p ⦄) = DivRem𝟎
  l {ℕ.𝐒(ℕ.𝐒(n))} ([∃]-intro (𝐒 k) ⦃ p ⦄) = DivRem𝐒 (l {n} ([∃]-intro k ⦃ injective(ℕ.𝐒) (injective(ℕ.𝐒) p) ⦄))

  r : Odd(n) → ∃(k ↦ (k ⋅ 2) + 1 ≡ n)
  r DivRem𝟎 = [∃]-intro 0
  r (DivRem𝐒 on) with [∃]-intro k ⦃ [≡]-intro ⦄ ← r on = [∃]-intro (𝐒(k))

{- TODO: All of these are special cases of [+]-of-[∣ᵣₑₘ], but it is not yet properly formalized
open import Numeral.Natural.Oper.Proofs

private variable a b d : ℕ

[+]-of-even-is-even : Even(a) → Even(b) → Even(a + b)
[+]-of-even-is-even ea DivRem𝟎      = ea
[+]-of-even-is-even ea (DivRem𝐒 eb) = DivRem𝐒 ([+]-of-even-is-even ea eb)

[+]-of-odd-is-even : Odd(a) → Odd(b) → Even(a + b)
{-[+]-of-odd-is-even DivRem𝟎 DivRem𝟎 = DivRem𝐒 DivRem𝟎
[+]-of-odd-is-even DivRem𝟎 (DivRem𝐒 x) = DivRem𝐒 ([+]-of-odd-is-even DivRem𝟎 x)
[+]-of-odd-is-even {_} {𝟎} (DivRem𝐒 x) eb = DivRem𝐒 ([+]-of-odd-is-even x eb)
[+]-of-odd-is-even {_} {𝐒 𝟎} (DivRem𝐒 x) eb = DivRem𝐒 ([+]-of-odd-is-even x DivRem𝟎)
[+]-of-odd-is-even {_} {𝐒 (𝐒 x)} (DivRem𝐒 DivRem𝟎) eb = [+]-of-odd-is-even (DivRem𝐒 DivRem𝟎) eb
[+]-of-odd-is-even {_} {𝐒 (𝐒 x)} (DivRem𝐒 (DivRem𝐒 x₁)) eb = [+]-of-odd-is-even (DivRem𝐒 (DivRem𝐒 x₁)) eb
-}


[+]-of-even-odd-is-odd : Even(a) → Odd(b) → Odd(a + b)
[+]-of-even-odd-is-odd ea ob = {!-c!}
-}
