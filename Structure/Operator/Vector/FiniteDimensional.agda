import      Lvl
open import Structure.Operator.Vector
open import Structure.Setoid.WithLvl
open import Type

module Structure.Operator.Vector.FiniteDimensional
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
open import Structure.Operator.Vector.LinearCombination ⦃ vectorSpace = vectorSpace ⦄
open import Syntax.Function

private variable n : ℕ

-- A sequence of vectors is linearly independent when there is no vector that can be represented as a linear combination by the others.
-- Note: Equivalent to: `∀{sf} → (linearCombination(vf)(sf) ≡ 𝟎ᵥ) → (sf ⊜ Vec.fill(𝟎ₛ))`.
LinearlyIndependent : Vec(n)(V) → Stmt
LinearlyIndependent = Injective ∘ linearCombination

-- A sequence of vectors is spanning the vector space when every vector in the vector space can be represented as a linear combination of the set of vectors.
Spanning : Vec(n)(V) → Stmt
Spanning = Surjective ∘ linearCombination

-- A sequence of vectors is a basis when every vector in the vector space can be represented as a unique linear combination of the set of vectors.
-- A sequence of vectors is a basis when they span the vector space and is linearly independent.
Basis : Vec(n)(V) → Stmt
Basis = Bijective ∘ linearCombination

-- A finite dimensional vector space is when there are a finite number of vectors that spans the whole space.
FiniteDimensional : Stmt
FiniteDimensional = ∃(n ↦ ∃(vf ↦ Spanning{n}(vf)))
