open import Logic
open import Logic.Classical
open import Structure.Setoid
open import Structure.OrderedField
open import Type

module Structure.Function.Metric
  {ℓF ℓₑF ℓ≤ ℓₘ ℓₑₘ}
  {F : Type{ℓF}} ⦃ equiv-F : Equiv{ℓₑF}(F) ⦄
  {_+_}{_⋅_}
  {_≤_ : _ → _ → Type{ℓ≤}}
  ⦃ orderedField-F : OrderedField{F = F}(_+_)(_⋅_)(_≤_) ⦄
  {M : Type{ℓₘ}} ⦃ equiv-M : Equiv{ℓₑₘ}(M) ⦄
  where

open OrderedField(orderedField-F)

import      Lvl
open import Functional as Fn
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Finite as 𝕟 using (𝕟)
open import Numeral.Natural as ℕ using (ℕ)
open import Sets.PredicateSet renaming (_≡_ to _≡ₛ_)
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Properties

private F₊ = ∃(Positive)
private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable x y z : M
private variable n : ℕ

record MetricSpace(d : M → M → F) : Type{ℓF Lvl.⊔ ℓ≤ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑₘ Lvl.⊔ ℓₑF} where
  field
    ⦃ distance-binary-operator ⦄ : BinaryOperator(d)
    self-distance : (d(x)(y) ≡ 𝟎) ↔ (x ≡ y)
    ⦃ distance-commutativity ⦄ : Commutativity(d)
    triangle-inequality : ((d(x)(y) + d(y)(z)) ≥ d(x)(z))

  -- A neighborhood of the center point p is the set of points within the radius r (all points around the center point in the radius).
  -- Also called: Open ball, open neighborhood.
  Neighborhood : M → F₊ → PredSet(M)
  Neighborhood(p)([∃]-intro r)(q) = (d(p)(q) < r)

  -- The set of all neighborhoods of a center point.
  Neighborhoods : M → PredSet(PredSet{ℓ}(M))
  Neighborhoods(p)(N) = ∃(r ↦ N ≡ₛ Neighborhood(p)(r))

  -- A punctured neighborhood is a neighborhood excluding the center point (all points around the center point except the center point in the radius).
  PuncturedNeighborhood : M → F₊ → PredSet(M)
  PuncturedNeighborhood(p)([∃]-intro r)(q) = (𝟎 < d(p)(q) < r)
