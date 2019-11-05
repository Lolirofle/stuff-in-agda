module Numeral.Natural.Relation.Divisibility where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic
open import Logic.Propositional
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Type

data Even : ℕ → Stmt{Lvl.𝟎} where
  instance
    Even0 : Even(𝟎)
    Even𝐒 : ∀{x : ℕ} → Even(x) → Even(𝐒(𝐒(x)))
{-# INJECTIVE Even #-}

data Odd : ℕ → Stmt{Lvl.𝟎} where
  instance
    Odd0 : Odd(𝐒(𝟎))
    Odd𝐒 : ∀{x : ℕ} → Odd(x) → Odd(𝐒(𝐒(x)))
{-# INJECTIVE Odd #-}

-- `(y ∣ x)` means that `y` is divisible by `x`.
-- In other words: `x/y` is an integer.
-- Or expressed in more elementary logic: `∃(c: ℕ). x = c⋅y`.
-- Note on the definition of Div𝐒:
--   The order (y + x) works and depends on rewriting rules of ℕ at the moment (Specifically on the commuted identity and successor rules, I think).
--   Without rewriting rules, deconstruction of Div𝐒 seems not working.
--   Example:
--     div23 : ¬(2 ∣ 3)
--     div23(Div𝐒())
--     This is a "valid" proof, but would not type-check because deconstruction from (2 ∣ 3) to (2 ∣ 1) is impossible.
--     Seems like the compiler would see (3 = 2+x), but because of definition of (_+_), only (3 = x+2) can be found.
--   Defining Div𝐒 with (x + y) inside would work, but then the definition of DivN becomes more complicated because (_⋅_) is defined in this order.
-- Note 2:
--   (0 ∣ 0) is true, and it is the only number divisible by 0.
-- TODO: Consider defining it like this instead: (Div𝟎 : ∀{y} → (𝐒(y) ∣ 𝟎))
data _∣_ : ℕ → ℕ → Stmt{Lvl.𝟎} where
  instance
    Div𝟎 : ∀{y}   → (y ∣ 𝟎)
    Div𝐒 : ∀{y x} → (y ∣ x) → (y ∣ (y + x))

_∤_ : ℕ → ℕ → Stmt
y ∤ x = ¬(y ∣ x)

-- `Divisor(n)(d)` means that `d` is a divisor of `n`.
Divisor = swap _∣_

-- Note: `(0 ∣ᵣₑₘ _)(_)` is impossible to construct.
data _∣ᵣₑₘ_ : (y : ℕ) → ℕ → 𝕟(y) → Stmt{Lvl.𝟎} where
  instance
    DivRem𝟎 : ∀{y : ℕ}  {r : 𝕟(𝐒(y))} → (𝐒(y) ∣ᵣₑₘ 𝕟-to-ℕ(r))(r)
    DivRem𝐒 : ∀{y x : ℕ}{r : 𝕟(𝐒(y))} → (𝐒(y) ∣ᵣₑₘ x)(r) → (𝐒(y) ∣ᵣₑₘ (𝐒(y) + x))(r)

_∣₊_ : ℕ → ℕ → Stmt
_∣₊_ 𝟎      x = ⊥
_∣₊_ (𝐒(y)) x = _∣_ (𝐒(y)) x
pattern Div₊𝟎 {x}    = Div𝟎 {x}
pattern Div₊𝐒 {x}{y} = Div𝐒 {x}{y}

data _[≡]_[mod]_ : ℕ → ℕ → ℕ → Stmt{Lvl.𝟎} where
  [≡mod]-i : ∀{x m   : ℕ} → (x [≡] x [mod] m)
  [≡mod]-l : ∀{x y m : ℕ} → (x [≡] y [mod] m) → ((x + m) [≡] y       [mod] m)
  [≡mod]-r : ∀{x y m : ℕ} → (x [≡] y [mod] m) → (x       [≡] (y + m) [mod] m)
