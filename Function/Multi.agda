module Function.Multi where

open import Data
open import Data.Tuple
open import Data.Tuple.Raise
import      Lvl
open import Numeral.Natural
open import Type

private variable ℓ : Lvl.Level

infixr 0 _⇉_

-- Construction of a multivariate function type (nested by repeated application of (_→_)) of different types from a tuple list of types.
-- Example:
--   ((A,B,C,D,..) ⇉ R)
--   = (A → (B → (C → (D → (.. → R)))))
--   = (A → B → C → D → .. → R)
-- Note:
--   This can be defined as:
--   `(As ⇉ B) = foldᵣ(_→ᶠ_) B As`
--   but it is not because apparently inference takes a hit.
-- TODO: Generalize. This is a relation for nested (_⟶_). One can also define a relation for nested (_⇉_). Currying would be different, but it is essentially the same thing. See for example the implementation of (_∘ₗ_) where 
_⇉_ : ∀{n : ℕ} → (Type{ℓ} ^ n) → Type{ℓ} → Type{ℓ}
_⇉_ {n = 𝟎}       _        B = B
_⇉_ {n = 𝐒(𝟎)}    A        B = A → B
_⇉_ {n = 𝐒(𝐒(n))} (A , As) B = A → (As ⇉ B)
