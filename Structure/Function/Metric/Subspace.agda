open import Logic
open import Logic.Classical
open import Structure.Function.Metric
open import Structure.Setoid
open import Structure.OrderedField
open import Type

module Structure.Function.Metric.Subspace
  {ℓF ℓₑF ℓ≤ ℓₘ ℓₑₘ}
  {F : Type{ℓF}} ⦃ equiv-F : Equiv{ℓₑF}(F) ⦄
  {_+_}{_⋅_}
  {_≤_ : _ → _ → Type{ℓ≤}}
  ⦃ orderedField-F : OrderedField{F = F}(_+_)(_⋅_)(_≤_) ⦄
  {M : Type{ℓₘ}} ⦃ equiv-M : Equiv{ℓₑₘ}(M) ⦄
  (d : M → M → F) ⦃ metric : MetricSpace(d) ⦄
  where

open MetricSpace(metric)
open OrderedField(orderedField-F)

import      Lvl
open import Logic.Propositional
open import Logic.Predicate
open import Sets.PredicateSet renaming (_≡_ to _≡ₛ_)
open import Syntax.Function

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level

-- A limit point of a subspace is a point "touching" the subspace without the point itself.
-- More formally, a point where all its punctured neighborhoods share points with the subspace.
-- Limit points are the following:
-- • Points strictly inside the subspace (note that this excludes isolated points).
-- • The "nearest" points outside the subspace.
LimitPoint : PredSet{ℓ}(M) → PredSet(M)
LimitPoint(E)(p) = ∀{r} → Overlapping(PuncturedNeighborhood(p)(r)) (E)

-- An isolated point of a subspace is a point in the subspace with no neighboring points.
-- An alternative informal definition is a point where its smallest punctured neighborhood is disjoint from the subspace.
IsolatedPoint : PredSet{ℓ}(M) → PredSet(M)
IsolatedPoint(E)(p) = (p ∈ E) ∧ ∃(r ↦ Disjoint(PuncturedNeighborhood(p)(r)) (E))

-- The interior of a subspace is the points strictly inside the subspace.
Interior : PredSet{ℓ}(M) → PredSet(M)
Interior(E)(p) = ∃(r ↦ Neighborhood(p)(r) ⊆ E)

-- The closure of a subspace is the subspace with its limit points.
Closure : PredSet{ℓ}(M) → PredSet(M)
Closure(E) = E ∪ LimitPoint(E)
