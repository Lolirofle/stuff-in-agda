module Function.Multi₌ where

open import Data
open import Data.Boolean
open import Data.Tuple
open import Data.Tuple.Raise
import      Data.Tuple.Raiseᵣ.Functions as Raise
open import Data.Tuple.RaiseTypeᵣ
open import Functional
import      Lvl
import      Lvl.MultiFunctions as Lvl
open import Numeral.Natural
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable n : ℕ

infixr 0 _⇉₌_

-- The type of a multivariate function (nested by repeated application of (_→_)) of different types but the same levels constructed by a tuple list of types.
-- Note:
--   It can also be defined as:
--   `(As ⇉ B) = foldᵣ(_→ᶠ_) B As`
--   `_⇉₌_ = Functional.swap(Raise.foldᵣ(_→ᶠ_))`
--   but then type inference will not work as well.
-- TODO: Generalize. This is a relation for nested (_⟶_). One can also define a relation for nested (_⇉_). Currying would be different, but it is essentially the same thing. See for example the implementation of (_∘ₗ_) where 
_⇉₌_ : (Type{ℓ} ^ n) → Type{ℓ} → Type{ℓ}
_⇉₌_ {n = 𝟎}       _        B = B
_⇉₌_ {n = 𝐒(𝟎)}    A        B = A → B
_⇉₌_ {n = 𝐒(𝐒(n))} (A , As) B = A → (As ⇉₌ B)
-- TODO: Cannot use _⇉_ to implement this special case? Level problems: `_⇉₌_ {ℓ}{n = n} As B = {!_⇉_ {n = n}{ℓ} (RaiseTypeᵣ.from-[^] As) B!}`
