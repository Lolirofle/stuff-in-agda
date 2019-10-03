module Type.Homotopy where

open import Relator.Equals
open import Type.Dependent
open import Type.Empty
open import Type.Unit

IsLevel : ℕ → Type → Stmt
IsLevel(𝟎)   (A) = IsUnit(A)
IsLevel(𝐒(n))(A) = ∀{x y : A} → IsLevel(n)(x ≡ y)

-- TODO: Where should this be stated?
ExcludedMiddle : Type → Stmt
ExcludedMiddle(A) = IsProp(A) → (IsEmpty(A) ∨ IsUnit(A))
