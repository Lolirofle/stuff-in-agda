module Data.List.Size where

import      Lvl
open import Data.List
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function.Domain
open import Type

open import Data.Boolean

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

-- TODO: For general types, not just Bool. 
index : (T → ℕ) → (List(T) → ℕ)
index f ∅       = 1
index f (x ⊰ l) = (2 ^ 𝐒(f(x))) ⋅ index f l -- TODO: 2 is temporary. Use unique primes (does not have to include all or even be in order).

{-
index-injective : ∀{f : T → ℕ} → ⦃ Injective(f) ⦄ → Injective(index f)
index-injective = {!!}
-}
