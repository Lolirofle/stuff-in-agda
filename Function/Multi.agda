module Function.Multi where

open import Data
open import Data.Tuple
open import Data.Tuple.Raise
open import Data.Tuple.RaiseTypeᵣ
open import Functional
import      Lvl
import      Lvl.MultiFunctions as Lvl
open import Numeral.Natural
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable n : ℕ

infixr 0 _⇉_

-- The type of a multivariate function (nested by repeated application of (_→_)) of different types and levels constructed by a tuple list of types.
-- This is useful when one needs a function of arbitrary length or by arbitrary argument types.
-- Essentially:
--   ((A,B,C,D,..) ⇉ R)
--   = (A → (B → (C → (D → (.. → R)))))
--   = (A → B → C → D → .. → R)
-- Example:
--   open import Syntax.Number
--   f : (Unit{0} , Unit{1} , Unit{2}) ⇉ Unit{3}
--   f <> <> <> = <>
_⇉_ : ∀{ℓ𝓈 : Lvl.Level ^ n} → Types(ℓ𝓈) → Type{ℓ} → Type{ℓ Lvl.⊔ (Lvl.⨆ ℓ𝓈)}
_⇉_ {n = 0}       _        B = B
_⇉_ {n = 1}       A        B = A → B
_⇉_ {n = 𝐒(𝐒(n))} (A , As) B = A → (As ⇉ B)
-- TODO: Does it work with Functional.swap(foldᵣ(_→ᶠ_)) ?
