open import Sets.Setoid
open import Structure.OrderedField
open import Type

module Structure.Function.Metric {ℓF ℓ≤} {F} ⦃ equiv-F : Equiv(F) ⦄ {_+_}{_⋅_}{_≤_} ⦃ orderedField-F : OrderedField{ℓF}{ℓ≤}{F}(_+_)(_⋅_)(_≤_) ⦄ where

open OrderedField(orderedField-F)

import      Lvl
open import Data.Boolean
open import Data.Boolean.Proofs
import      Data.Either as Either
open import Functional
open import Logic
open import Logic.Classical
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Ordering
open import Sets.PredicateSet renaming (_≡_ to _≡ₛ_)
open import Structure.Function.Ordering
open import Structure.Operator.Field
open import Structure.Operator.Monoid
open import Structure.Operator.Group
open import Structure.Operator.Proofs
open import Structure.Operator.Properties
open import Structure.Relator.Ordering
open        Structure.Relator.Ordering.Weak.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity

F₊ = ∃(NonNegative)

module _ where
  record MetricSpace {ℓ} {M : Type{ℓ}} ⦃ equiv-M : Equiv(M) ⦄ (d : M → M → F) : Type{ℓF Lvl.⊔ ℓ≤ Lvl.⊔ ℓ} where
    field
      self-distance : ∀{x y} → (d(x)(y) ≡ 𝟎) ↔ (x ≡ y)
      ⦃ distance-commutativity ⦄ : Commutativity(d)
      triangle-inequality : ∀{x y z} → (d(x)(z) ≤ (d(x)(y) + d(y)(z)))
      non-negativity : ∀{x y} → (d(x)(y) ≥ 𝟎)
      {-
      non-negativity{x}{y} =
        ([≤]ₗ-of-[+] (
          𝟎
          d(x)(x)
          d(x)(y) + d(y)(x)
          d(x)(y) + d(x)(y)
          2 ⋅ d(x)(y)
        ))
      -}

    -- [≤]ₗ-of-[+] ((x + y) ≤ z) → ((x ≤ z) ∨ (y ≤ z))

    Neighborhood : M → F₊ → PredSet(M)
    Neighborhood(p)([∃]-intro r)(q) = (d(p)(q) < r)

    Neighborhoods : ∀{ℓ} → M → PredSet(PredSet{ℓ}(M))
    Neighborhoods(p)(N) = ∃(r ↦ N ≡ₛ Neighborhood(p)(r))

    PuncturedNeighborhood : M → F₊ → PredSet(M)
    PuncturedNeighborhood(p)([∃]-intro r)(q) = (𝟎 < d(p)(q) < r)

    LimitPoint : ∀{ℓ} → PredSet{ℓ}(M) → PredSet(M)
    LimitPoint(E)(p) = ∀{r} → Overlapping(PuncturedNeighborhood(p)(r)) (E)

    IsolatedPoint : ∀{ℓ} → PredSet{ℓ}(M) → PredSet(M)
    IsolatedPoint(E)(p) = ∃(r ↦ Disjoint(PuncturedNeighborhood(p)(r)) (E))

    Interior : ∀{ℓ} → PredSet{ℓ}(M) → PredSet(M)
    Interior(E)(p) = ∃(r ↦ Neighborhood(p)(r) ⊆ E)

    Closed : ∀{ℓ} → PredSet(PredSet{ℓ}(M))
    Closed(E) = LimitPoint(E) ⊆ E

    Open : ∀{ℓ} → PredSet(PredSet{ℓ}(M))
    Open(E) = E ⊆ Interior(E)

    Perfect : ∀{ℓ} → PredSet(PredSet{ℓ}(M))
    Perfect(E) = LimitPoint(E) ≡ₛ E

    Bounded : ∀{ℓ} → PredSet(PredSet{ℓ}(M))
    Bounded(E) = ∃(p ↦ ∃(r ↦ E ⊆ Neighborhood(p)(r)))

    Discrete : ∀{ℓ} → PredSet(PredSet{ℓ}(M))
    Discrete(E) = E ⊆ IsolatedPoint(E)

    Closure : ∀{ℓ} → PredSet{ℓ}(M) → PredSet(M)
    Closure(E) = E ∪ LimitPoint(E)

    Dense : ∀{ℓ} → PredSet(PredSet{ℓ}(M))
    Dense(E) = ∀{p} → (p ∈ Closure(E))

    -- Compact

    Separated : ∀{ℓ₁ ℓ₂} → PredSet{ℓ₁}(M) → PredSet{ℓ₂}(M) → Stmt
    Separated(A)(B) = Disjoint(A)(Closure(B)) ∧ Disjoint(Closure(A))(B)

    Connected : ∀{ℓ} → PredSet{ℓ}(M) → Stmtω
    Connected(E) = ∀{ℓ₁ ℓ₂}{A : PredSet{ℓ₁}(M)}{B : PredSet{ℓ₂}(M)} → ((A ∪ B) ≡ₛ E) → Separated(A)(B) → ⊥

    -- Complete = Sequence.Cauchy ⊆ Sequence.Converging

    subneighborhood-radius : ∀{p₁ p₂}{r₁ r₂} → (Neighborhood(p₁)(r₁) ⊆ Neighborhood(p₂)(r₂)) ← (d(p₁)(p₂) ≤ ([∃]-witness r₂ − [∃]-witness r₁))
    subneighborhood-radius-on-same : ∀{p}{r₁ r₂} → (Neighborhood(p)(r₁) ⊆ Neighborhood(p)(r₂)) ↔ ([∃]-witness r₁ ≤ [∃]-witness r₂)

    neighborhood-is-open : ∀{p}{r} → Open(Neighborhood(p)(r))

    interior-is-largest-subspace : ∀{ℓ₁ ℓ₂}{E : PredSet{ℓ₁}(M)}{Eₛ : PredSet{ℓ₂}(M)} → Open(Eₛ) → (Eₛ ⊆ E) → (Eₛ ⊆ Interior(E))

    nested-interior : ∀{ℓ}{E : PredSet{ℓ}(M)} → Interior(Interior(E)) ≡ₛ Interior(E)

    isolated-limit-eq : ∀{ℓ}{E : PredSet{ℓ}(M)} → (IsolatedPoint(E) ⊆ ∅ {Lvl.𝟎}) ↔ (E ⊆ LimitPoint(E))

    interior-closure-eq1 : ∀{ℓ}{E : PredSet{ℓ}(M)} → ((∁ Interior(E)) ≡ₛ Closure(∁ E))

    interior-closure-eq2 : ∀{ℓ}{E : PredSet{ℓ}(M)} → (Interior(∁ E) ≡ₛ (∁ Closure(E)))

    open-closed-eq1 : ∀{ℓ}{E : PredSet{ℓ}(M)} → (Open(E) ↔ Closed(∁ E))

    open-closed-eq2 : ∀{ℓ}{E : PredSet{ℓ}(M)} → (Open(∁ E) ↔ Closed(E))

    union-is-open : ∀{ℓ₁ ℓ₂}{A : PredSet{ℓ₁}(M)}{B : PredSet{ℓ₂}(M)} → Open(A) → Open(B) → Open(A ∪ B)

    intersection-is-open : ∀{ℓ₁ ℓ₂}{A : PredSet{ℓ₁}(M)}{B : PredSet{ℓ₂}(M)} → Open(A) → Open(B) → Open(A ∩ B)

    -- open-subsubspace : ∀{ℓ₁ ℓ₂}{Eₛ : PredSet{ℓ₁}(M)}{E : PredSet{ℓ₂}(M)} → 

    separated-is-disjoint : ∀{ℓ₁ ℓ₂}{A : PredSet{ℓ₁}(M)}{B : PredSet{ℓ₂}(M)} → Separated(A)(B) → Disjoint(A)(B)

    unionₗ-is-connected : ∀{ℓ₁ ℓ₂}{A : PredSet{ℓ₁}(M)}{B : PredSet{ℓ₂}(M)} → Connected(A ∪ B) → Connected(A)

    unionᵣ-is-connected : ∀{ℓ₁ ℓ₂}{A : PredSet{ℓ₁}(M)}{B : PredSet{ℓ₂}(M)} → Connected(A ∪ B) → Connected(B)

    intersection-is-connected : ∀{ℓ₁ ℓ₂}{A : PredSet{ℓ₁}(M)}{B : PredSet{ℓ₂}(M)} → Connected(A) → Connected(B) → Connected(A ∩ B)

module Limit
  {ℓ₁ ℓ₂}
  {M₁ : Type{ℓ₁}} ⦃ equiv-M₁ : Equiv(M₁) ⦄ (d₁ : M₁ → M₁ → F)
  ⦃ space₁ : MetricSpace(d₁) ⦄
  {M₂ : Type{ℓ₂}} ⦃ equiv-M₂ : Equiv(M₂) ⦄ (d₂ : M₂ → M₂ → F)
  ⦃ space₂ : MetricSpace(d₂) ⦄
  where

  open MetricSpace

  Lim : ∀{ℓ}{E : PredSet{ℓ}(M₁)} → ((x : M₁) → ⦃ x ∈ E ⦄ → M₂) → M₁ → M₂ → Stmt
  Lim {E = E} f(p)(L) = ∃{Obj = F₊ → F₊}(δ ↦ ∀{ε : F₊}{x} → ⦃ ex : x ∈ E ⦄ → (p ∈ PuncturedNeighborhood(space₁)(x)(δ(ε))) → (L ∈ Neighborhood(space₂)(f(x) ⦃ ex ⦄)(ε)))

  lim : ∀{ℓ}{E : PredSet{ℓ}(M₁)} → (f : (x : M₁) → ⦃ x ∈ E ⦄ → M₂) → (p : M₁) → ⦃ ∃(Lim f(p)) ⦄ → M₂
  lim f(p) ⦃ [∃]-intro L ⦄ = L

  ContinuousOn : ∀{ℓ}{E : PredSet{ℓ}(M₁)} → ((x : M₁) → ⦃ x ∈ E ⦄ → M₂) → (p : M₁) → ⦃ p ∈ E ⦄ → Stmt
  ContinuousOn f(p) = Lim f(p) (f(p))

  Continuous : ∀{ℓ}{E : PredSet{ℓ}(M₁)} → ((x : M₁) → ⦃ x ∈ E ⦄ → M₂) → Stmt
  Continuous{E = E}(f) = ∀{p} → ⦃ ep : p ∈ E ⦄ → ContinuousOn f(p) ⦃ ep ⦄

  -- continuous-mapping-connected : Continuous(f) → Connected(E) → Connected(map f(E))
