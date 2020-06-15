import      Lvl
open import Structure.Operator.Vector
open import Structure.Setoid.WithLvl
open import Type

module Structure.Operator.Vector.LinearCombination
  {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ}
  {V : Type{ℓᵥ}} ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  {S : Type{ℓₛ}} ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  {_+ᵥ_ : V → V → V}
  {_⋅ₛᵥ_ : S → V → V}
  {_+ₛ_ _⋅ₛ_ : S → S → S}
  ⦃ vectorSpace : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) ⦄
  where

open VectorSpace(vectorSpace)

open import Data.Tuple using (_⨯_ ; _,_)
open import Functional using (id ; _∘_ ; _∘₂_ ; _$_ ; swap ; _on₂_)
open import Function.Equals
open import Logic
open import Logic.Predicate
open import Numeral.CoordinateVector as Vec using () renaming (Vector to Vec)
open import Numeral.Finite
open import Numeral.Natural
open import Sets.ExtensionalPredicateSet as PredSet using (PredSet ; _∈_ ; [∋]-binaryRelator)
open import Structure.Function.Domain
open import Syntax.Function

private variable ℓ ℓₗ : Lvl.Level
private variable n : ℕ

-- A linear combination constructed from a sequence of vectors and a sequence of scalars.
-- Linear combination of 0 scalars and vectors are the zero vector.
-- Linear combination of 1 scalar and vector is just scalar on vector multiplication.
-- Example: LinearCombination {4} sf vf = (sf[0] ⋅ₛᵥ vf[0]) +ᵥ (sf[1] ⋅ₛᵥ vf[1]) +ᵥ (sf[2] ⋅ₛᵥ vf[2]) +ᵥ (sf[3] ⋅ₛᵥ vf[3])
-- Inlined definition:
--   LinearCombination {0}       _  _  = 𝟎ᵥ
--   LinearCombination {1}       vf sf = Vec.proj(sf)(0) ⋅ₛᵥ Vec.proj(vf)(0)
--   LinearCombination {𝐒(𝐒(n))} vf sf = (Vec.proj(sf)(0) ⋅ₛᵥ Vec.proj(vf)(0)) +ᵥ (LinearCombination {𝐒(n)} (Vec.tail vf) (Vec.tail sf))
linearCombination : Vec(n)(V) → Vec(n)(S) → V
linearCombination = Vec.reduceOrᵣ(_+ᵥ_) 𝟎ᵥ ∘₂ Vec.map₂(_⋅ᵥₛ_)

-- Whether the two specified vectors are linearly dependent or not.
-- TODO: Is this definition neccessary?
LinearlyDependentPair : V → V → Stmt
LinearlyDependentPair v₁ v₂ = ∃{Obj = S ⨯ S}(\{(s₁ , s₂) → s₁ ⋅ₛᵥ v₁ ≡ s₂ ⋅ₛᵥ v₂})
