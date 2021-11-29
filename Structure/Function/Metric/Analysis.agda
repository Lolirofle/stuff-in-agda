open import Logic
open import Logic.Classical
open import Structure.Function.Metric
open import Structure.OrderedField
open import Structure.Setoid
open import Type

module Structure.Function.Metric.Analysis
  {ℓF ℓₑF ℓ≤ ℓₙ₀}
  {F : Type{ℓF}}
  ⦃ equiv-F : Equiv{ℓₑF}(F) ⦄
  {_+_}{_⋅_}
  {_≤_ : _ → _ → Type{ℓ≤}}
  ⦃ orderedField-F : OrderedField{F = F}{ℓₙ₀ = ℓₙ₀}(_+_)(_⋅_)(_≤_) ⦄
  where

open OrderedField(orderedField-F)

import      Lvl
open import Data.Boolean
open import Data.Boolean.Proofs
import      Data.Either as Either
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional as Fn
open import Functional.Instance
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Finite as 𝕟 using (𝕟)
open import Numeral.Natural as ℕ using (ℕ)
open import Sets.PredicateSet renaming (_≡_ to _≡ₛ_)
open import Structure.Setoid.Uniqueness
open import Structure.Function.Ordering
open import Structure.Operator.Proofs
open import Structure.Operator.Properties
open import Structure.Operator.Ring.Proofs
open import Structure.Operator
open import Structure.OrderedField.Min(_≤_) ⦃ infer ⦄
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Syntax.Implication
open import Syntax.Transitivity

private F₊ = ∃(Positive)

{-
module _
  {ℓₘ ℓₑₘ}
  {M : Type{ℓₘ}} ⦃ equiv-M : Equiv{ℓₑₘ}(M) ⦄
  (d : M → M → F) ⦃ metric : MetricSpace(d) ⦄
  where

  open MetricSpace(metric)

  private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
  private variable x y z : M
  private variable n : ℕ

  private variable p p₁ p₂ : M
  private variable E E₁ E₂ E₃ E₄ : PredSet{ℓ}(M)
  private variable Es : PredSet{ℓ₁}(PredSet{ℓ₂}(M))
  private variable r r₁ r₂ : F₊

  open import Logic.Predicate.Theorems
  open import Logic.Propositional.Theorems
  open import Structure.Function.Metric.Subspace d ⦃ metric ⦄
  open import Structure.Function.Metric.Subspace.Proofs d ⦃ metric ⦄
  open import Structure.Function.Metric.Subspace.Properties d ⦃ metric ⦄
  open import Structure.Relator
  open import Structure.Relator.Proofs
-}

module Sequence
  {ℓₘ ℓₑₘ}
  {M : Type{ℓₘ}} ⦃ equiv-M : Equiv{ℓₑₘ}(M) ⦄
  (d : M → M → F) ⦃ metric : MetricSpace(d) ⦄
  where
  open MetricSpace(metric)

  open import Numeral.Natural as ℕ using (ℕ)
  import      Numeral.Natural.Relation.Order as ℕ

  _≡ₗᵢₘ_ : (ℕ → M) → (ℕ → M) → Stmt
  f ≡ₗᵢₘ g = ∀{ε : F} → (ε > 𝟎) → ∃(N ↦ ∀{n} → (n ℕ.≥ N) → (d(f(n))(g(n)) < ε))

  ConvergesTo : (ℕ → M) → M → Stmt
  ConvergesTo f(L) = f ≡ₗᵢₘ (const L)

  Converging : (ℕ → M) → Stmt
  Converging(f) = ∃(ConvergesTo(f))

  Diverging : (ℕ → M) → Stmt
  Diverging(f) = ∀{L} → ¬(ConvergesTo f(L))

  lim : (f : ℕ → M) → ⦃ Converging(f) ⦄ → M
  lim(f) ⦃ [∃]-intro L ⦄ = L

  Cauchy : (ℕ → M) → Stmt
  Cauchy(f) = ∀{ε : F} → (ε > 𝟎) → ∃(N ↦ ∀{a b} → (a ℕ.≥ N) → (b ℕ.≥ N) → (d(f(a))(f(b)) < ε))

  Complete : Stmt
  Complete = Cauchy ⊆ Converging

  Bounded : (ℕ → M) → Stmt
  Bounded(f) = ∃(r ↦ ∃(p ↦ ∀{n} → (d(p)(f(n)) < r)))

  module _ ⦃ classical : ∀{ℓ}{P : Type{ℓ}} → Classical(P) ⦄ where
    open import Data
    open import Numeral.Natural.Equiv.Id
    import      Numeral.Natural.Function as ℕ
    open import Numeral.Natural.Function.Proofs
    open import Structure.Operator.Ring.Numerals        ⦃ ring = ring ⦄
    open import Structure.Operator.Ring.Numerals.Proofs ⦃ ring = ring ⦄
    open import Syntax.Number

    {-
    unique-converges-to : ∀{f} → Unique(ConvergesTo(f))
    unique-converges-to{f} {x}{y} cx cy = [¬¬]-elim \nxy →
      let ε = (d(x)(y) / 2) ⦃ {!!} ⦄
          [∃]-intro Nf ⦃ cf ⦄ = cx{ε} {!!}
          [∃]-intro Ng ⦃ cg ⦄ = cy{ε} {!!}
          N = ℕ.max Nf Ng
      in
      • cf{N} (max-orderₗ{Nf}{Ng})
      • cg{N} (max-orderᵣ{Nf}{Ng})
      ⇒₂-[ [<][+]-preserve ]
      ((d(f(N)) x + d(f(N)) y) < (ε + ε))  ⇒-[ swap(subtransitivityᵣ(_<_)(_≡_)) ({!symmetry(_≡_) ([⋅]-distributeᵣ-over-𝐒-iteration {2}{ε})!} 🝖 symmetry(_≡_) {!!}) ]
      ((d(f(N)) x + d(f(N)) y) < d(x)(y))  ⇒-[ subtransitivityₗ(_<_)(_≡_) (congruence₂ₗ(_+_)(d(f(N)) y) (commutativity(d))) ]
      ((d x (f(N)) + d(f(N)) y) < d(x)(y)) ⇒-[ subtransitivityₗ(_<_)(_≤_) triangle-inequality ]
      (d(x)(y) < d(x)(y))                  ⇒-[ irreflexivity(_<_) ]
      ⊥                                    ⇒-end

    converging-is-bounded : Converging ⊆ Bounded

    converging-is-cauchy : Converging ⊆ Cauchy
    -}

    -- strictly-ordered-sequence-limit : ∀{f g : ℕ → M} → (∀{n} → (f(n) < g(n))) → (lim f < lim g)
    -- ordered-sequence-limit : ∀{f g : ℕ → M} → (∀{n} → (f(n) ≤ g(n))) → (lim f ≤ lim g)

    -- limit-point-converging-sequence : ∀{E}{p} → LimitPoint(E)(p) → ∃(f ↦ (ConvergesTo f(p)) ∧ (∀{x} → (f(x) ∈ E)))

    -- TODO: Apparently, this requires both axiom of choice and excluded middle? At least the (←)-direction?
    -- continuous-sequence-convergence-composition : (ContinuousOn f(p)) ↔ (∀{g} → (ConvergesTo g(p)) → (ConvergesTo(f ∘ g)(f(p))))

  {-
  module Series where
    ∑ : (ℕ → M) → ℕ → M
    ∑ f(𝟎)    = 𝟎
    ∑ f(𝐒(n)) = (∑ f(n)) + f(𝐒(n))

    ∑₂ : (ℕ → M) → (ℕ ⨯ ℕ) → M
    ∑₂ f(a , b) = ∑ (f ∘ (a +_))(b − a)

    ConvergesTo : (ℕ → M) → M → Stmt
    ConvergesTo f(L) = Sequence.ConvergesTo(∑ f)(L)

    Converging : (ℕ → M) → Stmt
    Converging(f) = ∃(ConvergesTo(f))

    Diverging : (ℕ → M) → Stmt
    Diverging(f) = ∀{L} → ¬(ConvergesTo f(L))

    ConvergesTo : (ℕ → M) → M → Stmt
    AbsolutelyConvergesTo f(L) = ConvergesTo (‖_‖ ∘ f)(L)

    AbsolutelyConverging : (ℕ → M) → Stmt
    AbsolutelyConverging(f) = ∃(AbsolutelyConvergesTo(f))

    AbsolutelyDiverging : (ℕ → M) → Stmt
    AbsolutelyDiverging(f) = ∀{L} → ¬(AbsolutelyConvergesTo f(L))

    ConditionallyConverging : (ℕ → M) → Stmt
    ConditionallyConverging(f) = AbsolutelyDiverging(f) ∧ Converging(f)

    sequence-of-converging-series-converges-to-0 : Converging(f) → (Sequence.ConvergesTo f(𝟎))

    convergence-by-ordering : (∀{n} → f(n) ≤ g(n)) → (Converging(f) ← Converging(g))
    divergence-by-ordering : (∀{n} → f(n) ≤ g(n)) → (Diverging(f) → Diverging(g))
    convergence-by-quotient : Sequence.Converging(n ↦ f(n) / g(n)) → (Converging(f) ↔ Converging(g))
  -}

module Analysis
  {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂}
  {M₁ : Type{ℓ₁}} ⦃ equiv-M₁ : Equiv{ℓₑ₁}(M₁) ⦄ (d₁ : M₁ → M₁ → F)
  ⦃ space₁ : MetricSpace(d₁) ⦄
  {M₂ : Type{ℓ₂}} ⦃ equiv-M₂ : Equiv{ℓₑ₂}(M₂) ⦄ (d₂ : M₂ → M₂ → F)
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
