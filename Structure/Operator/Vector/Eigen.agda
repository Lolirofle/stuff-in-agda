import      Lvl
open import Structure.Operator.Vector
open import Structure.Setoid.WithLvl
open import Type

module Structure.Operator.Vector.Eigen
  {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ}
  {V : Type{ℓᵥ}} ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  {S : Type{ℓₛ}} ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (_+ᵥ_ : V → V → V)
  (_⋅ₛᵥ_ : S → V → V)
  (_+ₛ_ _⋅ₛ_ : S → S → S)
  ⦃ vectorSpace : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) ⦄
  where

open VectorSpace(vectorSpace)

open import Logic
open import Logic.Predicate
open import Logic.Propositional
open import Syntax.Function

-- v is a eigenvector for the eigenvalue 𝜆 of the linear transformation f.
-- Multiplication by an eigenvalue can replace a linear transformation for certain vectors.
Eigenpair : (V → V) → S → V → Stmt
Eigenpair(f)(𝜆)(v) = ((v ≢ 𝟎ᵥ) ∧ (f(v) ≡ 𝜆 ⋅ₛᵥ v))

Eigenvector : (V → V) → V → Stmt
Eigenvector(f)(v) = ∃(𝜆 ↦ Eigenpair(f)(𝜆)(v))

Eigenvalue : (V → V) → S → Stmt
Eigenvalue(f)(𝜆) = ∃(v ↦ Eigenpair(f)(𝜆)(v))
