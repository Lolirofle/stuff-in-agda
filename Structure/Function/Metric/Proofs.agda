open import Logic
open import Logic.Classical
open import Structure.Function.Metric
open import Structure.OrderedField
open import Structure.Setoid
open import Type

module Structure.Function.Metric.Proofs
  {ℓF ℓₑF ℓ≤ ℓₘ ℓₑₘ}
  {F : Type{ℓF}}
  ⦃ equiv-F : Equiv{ℓₑF}(F) ⦄
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
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Sets.PredicateSet renaming (_≡_ to _≡ₛ_)
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Operator.Ring.Proofs
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Implication
open import Syntax.Transitivity

private F₊ = ∃(Positive)

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable p p₁ p₂ : M
private variable E E₁ E₂ E₃ E₄ : PredSet{ℓ}(M)
private variable Es : PredSet{ℓ₁}(PredSet{ℓ₂}(M))
private variable r r₁ r₂ : F₊

distance-to-self : (d(p)(p) ≡ 𝟎)
distance-to-self = [↔]-to-[←] self-distance (reflexivity(_≡_))

instance
  non-negativity : NonNegative(d(p₁)(p₂))
  non-negativity{x}{y} = intro $
    (
      𝟎                 🝖[ _≡_ ]-[ symmetry(_≡_) distance-to-self ]-sub
      d(x)(x)           🝖[ _≤_ ]-[ triangle-inequality ]
      d(x)(y) + d(y)(x) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(d(x)(y)) (commutativity(d)) ]-sub
      d(x)(y) + d(x)(y) 🝖-end
    ) ⇒
    (𝟎 ≤ (d(x)(y) + d(x)(y)))                         ⇒-[ [≤][−]ₗ-preserve ]
    ((𝟎 − d(x)(y)) ≤ ((d(x)(y) + d(x)(y)) − d(x)(y))) ⇒-[ substitute₂(_≤_) (identityₗ(_+_)(𝟎)) (inverseOperᵣ(_+_)(_−_)) ]
    ((− d(x)(y)) ≤ d(x)(y))                           ⇒-[ [↔]-to-[←] [≤]-positive-by-self-negativity ]
    (𝟎 ≤ d(x)(y))                                     ⇒-end

neighborhood-contains-center : (p ∈ Neighborhood(p)(r))
neighborhood-contains-center {p}{[∃]-intro r ⦃ intro positive-r ⦄} =
  d(p)(p) 🝖[ _≡_ ]-[ distance-to-self ]-sub
  𝟎       🝖-semiend
  r       🝖-end-from-[ positive-r ]

-- TODO: When is this true?
-- subneighborhood-subradius : ∀{p₁ p₂}{r₁ r₂} → (Neighborhood(p₁)(r₁) ⊆ Neighborhood(p₂)(r₂)) → ([∃]-witness r₁ < [∃]-witness r₂)

subneighborhood-radius : (Neighborhood(p₁)(r₁) ⊆ Neighborhood(p₂)(r₂)) ← (d(p₂)(p₁) ≤ ([∃]-witness r₂ − [∃]-witness r₁))
subneighborhood-radius {p₁}{[∃]-intro r₁} {p₂}{[∃]-intro r₂} p {q} qN₁ =
  d(p₂)(q)             🝖[ _≤_ ]-[ triangle-inequality ]-sub
  d(p₂)(p₁) + d(p₁)(q) 🝖[ _<_ ]-[ [<][+]-preserve-subₗ p qN₁ ]-super
  (r₂ − r₁) + r₁       🝖[ _≡_ ]-[ inverseOperᵣ(_−_)(_+_) ⦃ [−][+]-inverseOperᵣ ⦄ {r₂}{r₁} ]
  r₂                   🝖-end

subneighborhood-radius-on-same : (Neighborhood(p)(r₁) ⊆ Neighborhood(p)(r₂)) ← ([∃]-witness r₁ ≤ [∃]-witness r₂)
subneighborhood-radius-on-same {p} {[∃]-intro r₁} {[∃]-intro r₂} r₁r₂ {x} xN₁ xN₂ = xN₁ (r₁r₂ 🝖 xN₂)

punctured-neighborhood-neighborhood-sub : PuncturedNeighborhood(p)(r) ⊆ Neighborhood(p)(r)
punctured-neighborhood-neighborhood-sub = [∧]-elimᵣ

punctured-neighborhood-neighborhood-eq : PuncturedNeighborhood(p)(r) ≡ₛ (Neighborhood(p)(r) ∖ (• p))
punctured-neighborhood-neighborhood-eq{r = r} = [↔]-intro right left where
  right = \([∧]-intro qN qp) → [∧]-intro ([≤][≢]-to-[<] (NonNegative.proof non-negativity) (contrapositiveᵣ([↔]-to-[→] self-distance) qp ∘ symmetry(_≡_))) qN
  left = \p → [∧]-intro (punctured-neighborhood-neighborhood-sub{r = r} p) (contrapositiveᵣ([↔]-to-[←] self-distance) (sub₂(_>_)(_≢_) ([∧]-elimₗ p)))
