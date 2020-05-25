module Syntax.Number where

import      Lvl
open import Logic.Propositional
open import Numeral.Natural
open import Type

record Numeral {ℓ} (T : Type{ℓ}) : Typeω where
  field
    {restriction-ℓ} : Lvl.Level
    restriction : ℕ → Type{restriction-ℓ}
    num : (n : ℕ) → ⦃ _ : restriction(n) ⦄ → T
open Numeral ⦃ ... ⦄ public using (num)
{-# BUILTIN FROMNAT num #-}

InfiniteNumeral = Numeral
module InfiniteNumeral {ℓ} {T : Type{ℓ}} where
  intro : (ℕ → T) → InfiniteNumeral(T)
  Numeral.restriction-ℓ (intro(_))         = Lvl.𝟎
  Numeral.restriction   (intro(_)) _       = ⊤
  Numeral.num           (intro(f)) n ⦃ _ ⦄ = f(n)

-- record InfiniteNumeral {ℓ} (T : Type{ℓ}) : Type{ℓ} where
-- record InfiniteNumeral {ℓ} (T : Type{ℓ}) : Type{ℓ} where
--   field
--     num : ℕ → T

-- instance
--   Numeral-from-InfiniteNumeral : ∀{ℓ}{T} → ⦃ _ : InfiniteNumeral{ℓ}(T) ⦄ → Numeral{ℓ}(T)
--   Numeral.restriction-ℓ ( Numeral-from-InfiniteNumeral ) = Lvl.𝟎
--   Numeral.restriction ( Numeral-from-InfiniteNumeral ) (_) = ⊤
--   num ⦃ Numeral-from-InfiniteNumeral ⦃ infNum ⦄ ⦄ (n) ⦃ _ ⦄ = InfiniteNumeral.num(infNum) (n)

instance
  ℕ-InfiniteNumeral : InfiniteNumeral (ℕ)
  ℕ-InfiniteNumeral = InfiniteNumeral.intro(id) where
    id : ℕ → ℕ
    id x = x

instance
  Level-InfiniteNumeral : InfiniteNumeral (Lvl.Level)
  Level-InfiniteNumeral = InfiniteNumeral.intro(f) where
    f : ℕ → Lvl.Level
    f(ℕ.𝟎)    = Lvl.𝟎
    f(ℕ.𝐒(n)) = Lvl.𝐒(f(n))



record NegativeNumeral {ℓ} (T : Type{ℓ}) : Typeω where
  field
    {restriction-ℓ} : Lvl.Level
    restriction : ℕ → Type{restriction-ℓ}
    num : (n : ℕ) → ⦃ _ : restriction(n) ⦄ → T
open NegativeNumeral ⦃ ... ⦄ public using () renaming (num to -num)
{-# BUILTIN FROMNEG -num #-}

InfiniteNegativeNumeral = NegativeNumeral
module InfiniteNegativeNumeral {ℓ} {T : Type{ℓ}} where
  intro : (ℕ → T) → InfiniteNegativeNumeral(T)
  NegativeNumeral.restriction-ℓ (intro(_))         = Lvl.𝟎
  NegativeNumeral.restriction   (intro(_)) _       = ⊤
  NegativeNumeral.num           (intro(f)) n ⦃ _ ⦄ = f(n)

-- record InfiniteNegativeNumeral {ℓ} (T : Type{ℓ}) : Type{ℓ} where
--   field
--     num : ℕ → T
-- open InfiniteNegativeNumeral ⦃ ... ⦄ public

-- instance
--   NegativeNumeral-from-InfiniteNegativeNumeral : ∀{ℓ}{T} → ⦃ _ : InfiniteNegativeNumeral{ℓ}(T) ⦄ → NegativeNumeral{ℓ}(T)
--   NegativeNumeral.restriction-ℓ ( NegativeNumeral-from-InfiniteNegativeNumeral ) = Lvl.𝟎
--   NegativeNumeral.restriction ( NegativeNumeral-from-InfiniteNegativeNumeral ) (_) = ⊤
--   -num ⦃ NegativeNumeral-from-InfiniteNegativeNumeral ⦃ infNegNum ⦄ ⦄ (n) ⦃ _ ⦄ = InfiniteNegativeNumeral.num(infNegNum) (n)
