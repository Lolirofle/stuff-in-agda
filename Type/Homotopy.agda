module Type.Homotopy {ℓ} where

open import Logic
open import Logic.Propositional
open import Numeral.Natural
open import Sets.Setoid hiding (_≡_)
open import Relator.Equals
open import Relator.Equals.Proofs.Equivalence
open import Type
open import Type.Dependent
open import Type.Empty
open import Type.Unit

IsLevel : ℕ → (A : Type{ℓ}) → Type
IsLevel(𝟎)   (A) = IsUnit(A)
IsLevel(𝐒(n))(A) = ∀{x y : A} → IsLevel(n)(x ≡ y)

-- TODO: Where should this be stated?
ExcludedMiddle : Type{ℓ} → Stmt
ExcludedMiddle(A) = IsProp(A) → (IsUnit(A) ∨ IsEmpty(A))
