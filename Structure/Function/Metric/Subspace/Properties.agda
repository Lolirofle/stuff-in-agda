open import Logic
open import Logic.Classical
open import Structure.Function.Metric
open import Structure.Setoid
open import Structure.OrderedField
open import Type

module Structure.Function.Metric.Subspace.Properties
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
open import Functional as Fn
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural as ℕ using (ℕ)
open import Sets.PredicateSet renaming (_≡_ to _≡ₛ_)
open import Structure.Function.Metric.Subspace d ⦃ metric ⦄

private F₊ = ∃(Positive)
private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable x y z : M
private variable n : ℕ

-- A subspace is closed when it contains all of its limit points.
Closed : PredSet(PredSet{ℓ}(M))
Closed(E) = LimitPoint(E) ⊆ E

-- A subspace is open when it is its own interior.
Open : PredSet(PredSet{ℓ}(M))
Open(E) = E ⊆ Interior(E)

-- A subspace is perfect when it includes all its limit points (when it is closed) and have no isolated points.
Perfect : PredSet(PredSet{ℓ}(M))
Perfect(E) = LimitPoint(E) ≡ₛ E

-- A subspace is bounded when there are points in every direction such that there are no more points further away from them.
-- More formally, when there is a neighborhood greater than the subspace. This works because a neighborhood is bounded by definition.
Bounded : PredSet(PredSet{ℓ}(M))
Bounded(E) = ∃(p ↦ ∃(r ↦ E ⊆ Neighborhood(p)(r)))

-- A subspace is discrete when it only contains isolated points.
Discrete : PredSet(PredSet{ℓ}(M))
Discrete(E) = E ⊆ IsolatedPoint(E)

-- A subspace is dense when all points of the space is either in the subspace or is a limit point of the subspace.
Dense : PredSet(PredSet{ℓ}(M))
Dense(E) = ∀{p} → (p ∈ Closure(E))

-- Compact

Separated : PredSet{ℓ₁}(M) → PredSet{ℓ₂}(M) → Stmt
Separated(A)(B) = Disjoint(A)(Closure(B)) ∧ Disjoint(Closure(A))(B)

Connected : PredSet{ℓ}(M) → Stmtω
Connected(E) = ∀{ℓ₁ ℓ₂}{A : PredSet{ℓ₁}(M)}{B : PredSet{ℓ₂}(M)} → ((A ∪ B) ≡ₛ E) → Separated(A)(B) → ⊥

-- Complete = Sequence.Cauchy ⊆ Sequence.Converging
