module Data.List.Functions.Multi where

import      Lvl
open import Data
open import Data.List
open import Data.List.Functions hiding (separate)
open import Data.Option
open import Data.Tuple
open import Data.Tuple.Raise
import      Data.Tuple.Raiseᵣ.Functions as Raise
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Oper.Modulo
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

-- TODO: Also called zip in other languages
-- module _ where
--   open import Data.Tuple.Raise as Tuple using (_^_)
--   open import Function.Multi as Multi using (_⇉_)

  --map₊ : ∀{n}{As : Type{ℓ} ^ n}{B} → (As ⇉ B) → (Tuple.map List(As) ⇉ List(B))
  -- map₊ {n = 𝟎}                 = const ∅
  -- map₊ {n = 𝐒(𝟎)}              = map
  -- map₊ {n = 𝐒(𝐒(n))} _ ∅       = Multi.const ∅
  -- map₊ {n = 𝐒(𝐒(n))} f (x ⊰ l) = {!!}

{-
separate : (n : ℕ) → List(T) → (List(T) ^ n)
separate(0)       _ = <>
separate(1)       l = l
separate(𝐒(𝐒(n))) l = {!!}
-- Raise.repeat (𝐒(𝐒(n))) ∅
-- (x ⊰ l) = Raise.map₂ {!skip!} {!!} (∅ , separate(𝐒(n)) l)
-}

-- Separates a list by a function assigning which list index it should lie in.
-- Example:
--   separateBy(_mod 3) [0,1,2,3,4,5,6,7,8,9] = [[0,3,6,9] , [1,4,7] , [2,5,8]]
separateBy : ∀{n} → (T → 𝕟(n)) → List(T) → (List(T) ^ n)
separateBy f ∅       = Raise.repeat _ ∅
separateBy f (x ⊰ l) = Raise.updateAt (f(x)) (x ⊰_) (separateBy f l)
