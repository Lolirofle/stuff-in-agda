module Syntax.Number where

open import Data
open import Function
import      Lvl
open import Numeral.Natural
open import Numeral.Natural.Induction
open import Type

private variable ℓ ℓᵣ : Lvl.Level

-- A numeral allows the syntactical conversion from some natural numbers to its inhabitants.
-- The restriction restricts which natural numbers that are able to represent inhabitants.
record Numeral (T : Type{ℓ}) (R : ℕ → Type{ℓᵣ}) : Type{ℓ Lvl.⊔ ℓᵣ} where
  Restriction = R
  field num : (n : ℕ) → ⦃ restriction : Restriction(n) ⦄ → T

-- An infinite numeral allows the syntactical conversion from any natural numbers to its inhabitants.
InfiniteNumeral : (T : Type{ℓ}) → Type
InfiniteNumeral(T) = Numeral(T) (const(Unit{Lvl.𝟎}))
module InfiniteNumeral {T : Type{ℓ}} where
  intro : (ℕ → T) → InfiniteNumeral(T)
  Numeral.num(intro(f)) n = f(n)

  num : ⦃ InfiniteNumeral(T) ⦄ → ℕ → T
  num ⦃ num ⦄ n = Numeral.num num n

-- A negative numeral allows the syntactical conversion from some negative natural numbers to its inhabitants.
-- This is similar to Numeral. The difference is that it converts natural numbers with a negative sign in front syntactically.
record NegativeNumeral (T : Type{ℓ}) (R : ℕ → Type{ℓᵣ}) : Type{ℓ Lvl.⊔ ℓᵣ} where
  Restriction = R
  field num : (n : ℕ) → ⦃ restriction : Restriction(n) ⦄ → T

-- An infinite numeral allows the syntactical conversion from any negative natural numbers to its inhabitants.
InfiniteNegativeNumeral : (T : Type{ℓ}) → Type
InfiniteNegativeNumeral(T) = NegativeNumeral(T) (const(Unit{Lvl.𝟎}))
module InfiniteNegativeNumeral {T : Type{ℓ}} where
  intro : (ℕ → T) → InfiniteNegativeNumeral(T)
  NegativeNumeral.num(intro(f)) n = f(n)

  num : ⦃ InfiniteNegativeNumeral(T) ⦄ → ℕ → T
  num ⦃ num ⦄ n = NegativeNumeral.num num n



open Numeral ⦃ ... ⦄ public using (num)
{-# BUILTIN FROMNAT num #-}

open NegativeNumeral ⦃ ... ⦄ public using () renaming (num to -num)
{-# BUILTIN FROMNEG -num #-}



instance
  ℕ-InfiniteNumeral : InfiniteNumeral(ℕ)
  ℕ-InfiniteNumeral = InfiniteNumeral.intro id

instance
  Level-InfiniteNumeral : InfiniteNumeral(Lvl.Level)
  Level-InfiniteNumeral = InfiniteNumeral.intro(ℕ-elim _ Lvl.𝟎 (const Lvl.𝐒))
