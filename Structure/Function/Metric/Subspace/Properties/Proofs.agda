open import Logic
open import Logic.Classical
open import Structure.Function.Metric
open import Structure.OrderedField
open import Structure.Setoid
open import Type

module Structure.Function.Metric.Subspace.Properties.Proofs
  {ℓF ℓₑF ℓ≤}
  {F : Type{ℓF}}
  ⦃ equiv-F : Equiv{ℓₑF}(F) ⦄
  {_+_}{_⋅_}
  {_≤_ : _ → _ → Type{ℓ≤}}
  ⦃ orderedField-F : OrderedField{F = F}(_+_)(_⋅_)(_≤_) ⦄
  where

open OrderedField(orderedField-F)

import      Lvl
open import Data.Boolean
open import Data.Boolean.Proofs
import      Data.Either as Either
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional as Fn
open import Lang.Instance
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

  Closed-function : (E₁ ≡ₛ E₂) → (Closed(E₁) ↔ Closed(E₂))
  Closed-function eq = [↔]-intro
    (\cl → [↔]-to-[←] eq ∘ cl ∘ [⊆]-with-LimitPoint ([↔]-to-[→] eq))
    (\cl → [↔]-to-[→] eq ∘ cl ∘ [⊆]-with-LimitPoint ([↔]-to-[←] eq))

  Open-function : (E₁ ≡ₛ E₂) → (Open(E₁) ↔ Open(E₂))
  Open-function eq = [↔]-intro
    (\o{x} → [⊆]-with-Interior ([↔]-to-[←] eq) ∘ o{x} ∘ [↔]-to-[→] eq)
    (\o{x} → [⊆]-with-Interior ([↔]-to-[→] eq) ∘ o{x} ∘ [↔]-to-[←] eq)

  neighborhood-is-open : Open(Neighborhood(p)(r))
  neighborhood-is-open {p}{r}{x} = [≡]-to-[⊇] (neighborhood-interior-is-self{p}{r}{x}) {x}

  universal-open : Open(𝐔 {ℓ})
  universal-open _ = [∃]-intro ([∃]-intro 𝟏 ⦃ intro [<]-identities ⦄) ⦃ \_ → [⊤]-intro ⦄

  empty-open : Open(∅ {ℓ})
  empty-open ()

  universal-closed : Closed(𝐔 {ℓ})
  universal-closed = \_ → [⊤]-intro

  empty-closed : Closed(∅ {ℓ})
  empty-closed xLp∅ with [∃]-intro _ ⦃ [∧]-intro _ () ⦄ ← xLp∅{[∃]-intro 𝟏 ⦃ intro [<]-identities ⦄}

  interior-is-open : Open(Interior(E))
  interior-is-open = [↔]-to-[←] interior-idempotence

  closed-closure-subset : Closed(E) ↔ (Closure(E) ⊆ E)
  closed-closure-subset {E = E} = [↔]-intro left right where
    left : Closed(E) ← (Closure(E) ⊆ E)
    left clEE = clEE ∘ \p → [∨]-introᵣ(\{r} → p{r})

    right : Closed(E) → (Closure(E) ⊆ E)
    right cl {x} (Either.Left  xE)   = xE
    right cl {x} (Either.Right xLpE) = cl(\{r} → xLpE{r})

  union-is-open : Open(E₁) → Open(E₂) → Open(E₁ ∪ E₂)
  union-is-open o1 o2 (Either.Left  xE₁) with [∃]-intro r₁ ⦃ o₁ ⦄ ← o1 xE₁ = [∃]-intro r₁ ⦃ Either.Left ∘ o₁ ⦄
  union-is-open o1 o2 (Either.Right xE₂) with [∃]-intro r₂ ⦃ o₂ ⦄ ← o2 xE₂ = [∃]-intro r₂ ⦃ Either.Right ∘ o₂ ⦄

  big-union-is-open : (∀{E} → (E ∈ Es) → Open(E)) → Open(⋃ Es)
  big-union-is-open Eo ([∃]-intro E ⦃ [∧]-intro EEs xE ⦄) with [∃]-intro r ⦃ o ⦄ ← Eo EEs xE = [∃]-intro r ⦃ (xE ↦ [∃]-intro E ⦃ [∧]-intro EEs xE ⦄) ∘ o ⦄

  -- TODO: Move
  min-positive : ∀{x y} → ⦃ Positive(x) ⦄ → ⦃ Positive(y) ⦄ → Positive(min x y)
  min-positive ⦃ intro px ⦄ ⦃ intro py ⦄ = intro (min-intro(_> 𝟎) (const px) (const py))

  intersection-is-open : Open(E₁) → Open(E₂) → Open(E₁ ∩ E₂)
  intersection-is-open o1 o2 ([∧]-intro xE₁ xE₂)
    with [∃]-intro ([∃]-intro r₁ ⦃ pos1 ⦄) ⦃ o₁ ⦄ ← o1 xE₁
    with [∃]-intro ([∃]-intro r₂ ⦃ pos2 ⦄) ⦃ o₂ ⦄ ← o2 xE₂
    = [∃]-intro ([∃]-intro (min r₁ r₂) ⦃ min-positive ⦄) ⦃ \dmin → [∧]-intro
      (o₁(subtransitivityᵣ(_<_)(_≤_) dmin ([∧]-elimₗ min-correctness)))
      (o₂(subtransitivityᵣ(_<_)(_≤_) dmin ([∧]-elimᵣ min-correctness)))
    ⦄

  module _ ⦃ classical : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P) ⦄ where
    closure-is-closed : ⦃ UnaryRelator(E) ⦄ → Closed(Closure(E))
    closure-is-closed {x = p} pLpClE = [↔]-to-[←] closure-membership \{r@([∃]-intro R ⦃ pos-R ⦄)} →
      let [∃]-intro x ⦃ [∧]-intro xNeigh xClE ⦄ = pLpClE{r}
      in overlapping-super
        (\{y} yNeigh →
          d(p)(y)                 🝖[ _≡_ ]-[ commutativity(d) ]-sub        
          d(y)(p)                 🝖[ _≤_ ]-[ triangle-inequality ]-sub
          (d(y)(x) + d(x)(p))     🝖[ _≡_ ]-[ congruence₂(_+_) (commutativity(d)) (commutativity(d)) ]-sub
          (d(x)(y) + d(p)(x))     🝖[ _<_ ]-[ [<][+]-preserveₗ yNeigh ]-super
          (R − d(p)(x)) + d(p)(x) 🝖[ _≡_ ]-[ inverseOperᵣ(_−_)(_+_) ⦃ [−][+]-inverseOperᵣ ⦄ ]
          R                       🝖-end
        )
        id
        ([↔]-to-[→] closure-membership xClE {[∃]-intro (R − d(p)(x)) ⦃ intro ([↔]-to-[←] [<]-positive-difference ([∧]-elimᵣ xNeigh)) ⦄})

    -- All points in the closure of the subspace are either isolated points or limit points.
    isolated-xor-limit-is-closure-point : (IsolatedPoint(E) ▵ LimitPoint(E)) ≡ₛ Closure(E)
    isolated-xor-limit-is-closure-point {E = E} = [⊇][⊆]-to-[≡] (\{p} → left{p}) (\{p} → isolated-or-limit-closure-point-sub{x = p} ∘ [⊕]-to-[∨]) where
      left : Closure(E) ⊆ (IsolatedPoint(E) ▵ LimitPoint(E))
      left {p} = [∨]-elim (\pE → [⊕]-or-not-both (or pE) isolated-limit-disjoint) (\lp → [⊕]-introᵣ (\{r} → lp{r}) (\p → isolated-limit-disjoint ([∧]-intro p \{r} → lp{r}))) where
        or : E ⊆ (IsolatedPoint(E) ∪ LimitPoint(E))
        or {p} pE = [¬→]-disjunctive-formᵣ ⦃ classical ⦄ $
          ¬(p ∈ IsolatedPoint(E))                                       ⇒-[]
          ¬((p ∈ E) ∧ ∃(r ↦ Disjoint(PuncturedNeighborhood(p)(r)) (E))) ⇒-[ [¬]-preserves-[∧][∨]ᵣ ]
          (p ∉ E) ∨ ¬ ∃(r ↦ Disjoint(PuncturedNeighborhood(p)(r)) (E))  ⇒-[ swap [∨]-not-left ([¬¬]-intro pE) ]
          ¬ ∃(r ↦ Disjoint(PuncturedNeighborhood(p)(r)) (E))            ⇒-[ [¬∃]-to-[∀¬] ]
          (∀{r} → ¬ Disjoint(PuncturedNeighborhood(p)(r)) (E))          ⇒-[ (\p {r} → [⊕]-not-not-right disjoint-xor-overlapping (p{r})) ]
          (∀{r} → Overlapping(PuncturedNeighborhood(p)(r)) (E))         ⇒-[]
          p ∈ LimitPoint E                                              ⇒-end

    open-closed-eq1 : ⦃ UnaryRelator(E) ⦄ → (Open(E) ↔ Closed(∁ E))
    open-closed-eq1 {E = E} = [↔]-intro ([¬¬]-elim ∘ left) ([¬¬]-elim ∘ right) where
      right : Open E → (¬ Closed (∁ E)) → ⊥
      right op ncl
        with [∃]-intro p ⦃ [∧]-intro pLP∁E pE ⦄ ← ncl ⇒
          ¬(Closed (∁ E))                           ⇒-[]
          ¬(LimitPoint(∁ E) ⊆ (∁ E))                ⇒-[ [¬∀]-to-[∃¬] ⦃ classical ⦄ ]
          ∃(p ↦ ¬((p ∈ LimitPoint(∁ E)) → (p ∉ E))) ⇒-[ [∃]-map-proof ([¬→][∧]ᵣ ⦃ classical ⦄ ⦃ classical ⦄)  ]
          ∃(p ↦ (p ∈ LimitPoint(∁ E)) ∧ ¬¬(p ∈ E))  ⇒-[ [∃]-map-proof ([∧]-map id [¬¬]-elim) ]
          ∃(p ↦ (p ∈ LimitPoint(∁ E)) ∧ (p ∈ E))    ⇒-end
        with [∃]-intro R@([∃]-intro r ⦃ nz-r ⦄) ⦃ NpE ⦄ ← op pE
        with [∃]-intro q ⦃ [∧]-intro ([∧]-intro zd dr) nqE ⦄ ← pLP∁E{R}
        =
        • (NpE{q} ⇒
          ((d(p)(q) < r) → (q ∈ E)) ⇒-[ apply dr ]
          (q ∈ E)                   ⇒-end
        )
        • (nqE ⇒
          (q ∉ E) ⇒-end
        ) ⇒₂-[ apply ]
        ⊥ ⇒-end

      left : Closed(∁ E) → (¬ Open(E)) → ⊥
      left cl nop =
        nop ⇒
        ¬ Open(E)                                                      ⇒-[]
        ¬(E ⊆ Interior(E))                                             ⇒-[ [↔]-to-[→] [⊈]-to-overlapping-complement ]
        Overlapping(E)(∁(Interior(E)))                                 ⇒-[]
        ∃(p ↦ (p ∈ E) ∧ (p ∉ Interior(E)))                             ⇒-[]
        ∃(p ↦ (p ∈ E) ∧ ¬ ∃(r ↦ Neighborhood(p)(r) ⊆ E))               ⇒-[ [∃]-map-proof (\{x} → [∧]-map id [¬∃]-to-[∀¬]) ]
        ∃(p ↦ (p ∈ E) ∧ (∀{r} → ¬(Neighborhood(p)(r) ⊆ E)))            ⇒-[ [∃]-map-proof (\{x} → [∧]-map id \prev {q} → [↔]-to-[→] [⊈]-to-overlapping-complement (prev{q})) ]
        ∃(p ↦ (p ∈ E) ∧ (∀{r} → Overlapping(Neighborhood(p)(r))(∁ E))) ⇒-[ [∃]-map-proof (\{x} → [∧]-map id ([↔]-to-[←] (closure-membership ⦃ classical ⦄ ⦃ [¬]-unaryRelator ⦄))) ]
        ∃(p ↦ (p ∈ E) ∧ (p ∈ Closure(∁ E)))                            ⇒-[ [∃]-map-proof (\{x} → [∧]-map id ([↔]-to-[→] closed-closure-subset cl)) ]
        ∃(p ↦ (p ∈ E) ∧ (p ∈ (∁ E)))                                   ⇒-[ [∃]-map-proof (Tuple.uncurry apply) ]
        ∃(p ↦ ⊥)                                                       ⇒-[ [∃]-proof ]
        ⊥                                                              ⇒-end

    open-closed-eq2 : ⦃ UnaryRelator(E) ⦄ → (Open(∁ E) ↔ Closed(E))
    open-closed-eq2 = [↔]-transitivity (open-closed-eq1 ⦃ [¬]-unaryRelator ⦄) (Closed-function ([↔]-intro [¬¬]-intro [¬¬]-elim))

    -- TODO: Move
    [∁]-preserves-[∪][∩] : ((∁(E₁ ∪ E₂)) ≡ₛ ((∁ E₁) ∩ (∁ E₂)))
    [∁]-preserves-[∪][∩] = [¬]-preserves-[∨][∧]

    [∁]-preserves-[∩][∪] : ((∁(E₁ ∩ E₂)) ≡ₛ ((∁ E₁) ∪ (∁ E₂)))
    [∁]-preserves-[∩][∪] = [¬]-preserves-[∧][∨]

    [∁]-preserves-[⋂][⋃] : ⦃ rel : UnaryRelator ⦃ intro(_≡ₛ_) ⦃ [≡]-equivalence ⦄ ⦄ Es ⦄ → (∁(⋂ Es) ≡ₛ ⋃(unmap ∁(Es)))
    [∁]-preserves-[⋂][⋃] {Es = Es} ⦃ rel = rel ⦄ = [↔]-intro
      (\([∃]-intro E ⦃ [∧]-intro p q ⦄) a → a p q)
      ([∃]-map ∁ ([∧]-map (substitute₁ ⦃ _ ⦄ (Es) ⦃ rel ⦄ double-negation) id ∘ [¬→][∧]ᵣ) ∘ ([¬∀]-to-[∃¬] ⦃ classical ⦄))

    [∁]-preserves-[⋃][⋂] : ⦃ rel : UnaryRelator ⦃ intro(_≡ₛ_) ⦃ [≡]-equivalence ⦄ ⦄ Es ⦄ → (∁(⋃ Es) ≡ₛ ⋂(unmap ∁(Es)))
    [∁]-preserves-[⋃][⋂] {Es = Es} ⦃ rel = rel ⦄ = [↔]-intro
      (\a ([∃]-intro E ⦃ [∧]-intro p q ⦄) → a{∁ E} (substitute₁ ⦃ _ ⦄ (Es) ⦃ rel ⦄ double-negation p) q)
      (\ne {E} EnEs → [¬¬]-elim \nxE → ne ([∃]-intro (∁ E) ⦃ [∧]-intro EnEs nxE ⦄))

    instance
      UnaryRelator-unaryRelator : ∀{ℓ ℓₑ ℓₗ}{T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → UnaryRelator ⦃ intro(_≡ₛ_ {ℓₗ}) ⦃ [≡]-equivalence ⦄ ⦄ (UnaryRelator{A = T})
      UnaryRelator.substitution UnaryRelator-unaryRelator PQ (intro relP) = intro \xy → [↔]-to-[→] PQ ∘ relP xy ∘ [↔]-to-[←] PQ

    union-is-closed : ⦃ UnaryRelator(E₁) ⦄ → ⦃ UnaryRelator(E₂) ⦄ → Closed(E₁) → Closed(E₂) → Closed(E₁ ∪ E₂)
    union-is-closed {E₁ = E₁}{E₂ = E₂} cl1 cl2 = [↔]-to-[→] (open-closed-eq2 ⦃ [∨]-unaryRelator ⦄) ([↔]-to-[→] (Open-function (symmetry(_≡ₛ_) (\{x} → [∁]-preserves-[∪][∩] {E₁ = E₁}{E₂ = E₂}{x}))) (intersection-is-open ([↔]-to-[←] open-closed-eq2 cl1) ([↔]-to-[←] open-closed-eq2 cl2)))

    intersection-is-closed : ⦃ UnaryRelator(E₁) ⦄ → ⦃ UnaryRelator(E₂) ⦄ → Closed(E₁) → Closed(E₂) → Closed(E₁ ∩ E₂)
    intersection-is-closed {E₁ = E₁}{E₂ = E₂} cl1 cl2 = [↔]-to-[→] (open-closed-eq2 ⦃ [∧]-unaryRelator ⦄) ([↔]-to-[→] (Open-function (symmetry(_≡ₛ_) (\{x} → [∁]-preserves-[∩][∪] {E₁ = E₁}{E₂ = E₂}{x}))) (union-is-open ([↔]-to-[←] open-closed-eq2 cl1) ([↔]-to-[←] open-closed-eq2 cl2)))

    big-intersection-is-closed : ⦃ rel : UnaryRelator ⦃ intro(_≡ₛ_) ⦃ [≡]-equivalence ⦄ ⦄ Es ⦄ → (∀{E} → (E ∈ Es) → UnaryRelator(E)) → (∀{E} → (E ∈ Es) → Closed(E)) → Closed(⋂ Es)
    big-intersection-is-closed {Es = Es} ⦃ rel = rel ⦄ rel-E Ec = [↔]-to-[→] (open-closed-eq2 ⦃ [∀]-unaryRelator ⦃ rel-P = [→]-dependent-unaryRelator rel-E ⦄ ⦄) ([↔]-to-[→] (Open-function (symmetry(_≡ₛ_) (\{x} → [∁]-preserves-[⋂][⋃] {Es = Es}{x}))) (big-union-is-open \{E} p → [↔]-to-[←] (open-closed-eq1 ⦃ substitute₁ ⦃ _ ⦄ (UnaryRelator) ⦃ UnaryRelator-unaryRelator ⦄ (\{x} → [↔]-symmetry (double-negation ⦃ classical ⦄)) ([¬]-unaryRelator ⦃ rel-P = rel-E p ⦄) ⦄) (Ec{∁ E} p)))

{-
    interior-is-largest-open-subspace : ∀{ℓ₁ ℓ₂}{E : PredSet{ℓ₁}(M)}{Eₛ : PredSet{ℓ₂}(M)} → Open(Eₛ) → (Eₛ ⊆ E) → (Eₛ ⊆ Interior(E))

    isolated-limit-eq : ∀{ℓ}{E : PredSet{ℓ}(M)} → (IsolatedPoint(E) ⊆ ∅ {Lvl.𝟎}) ↔ (E ⊆ LimitPoint(E))

    interior-closure-eq1 : ∀{ℓ}{E : PredSet{ℓ}(M)} → ((∁ Interior(E)) ≡ₛ Closure(∁ E))

    interior-closure-eq2 : ∀{ℓ}{E : PredSet{ℓ}(M)} → (Interior(∁ E) ≡ₛ (∁ Closure(E)))

    -- open-subsubspace : ∀{ℓ₁ ℓ₂}{Eₛ : PredSet{ℓ₁}(M)}{E : PredSet{ℓ₂}(M)} → 

    separated-is-disjoint : ∀{ℓ₁ ℓ₂}{A : PredSet{ℓ₁}(M)}{B : PredSet{ℓ₂}(M)} → Separated(A)(B) → Disjoint(A)(B)

    unionₗ-is-connected : ∀{ℓ₁ ℓ₂}{A : PredSet{ℓ₁}(M)}{B : PredSet{ℓ₂}(M)} → Connected(A ∪ B) → Connected(A)

    unionᵣ-is-connected : ∀{ℓ₁ ℓ₂}{A : PredSet{ℓ₁}(M)}{B : PredSet{ℓ₂}(M)} → Connected(A ∪ B) → Connected(B)

    intersection-is-connected : ∀{ℓ₁ ℓ₂}{A : PredSet{ℓ₁}(M)}{B : PredSet{ℓ₂}(M)} → Connected(A) → Connected(B) → Connected(A ∩ B)

module Sequence {ℓ} {M : Type{ℓ}} ⦃ equiv-M : Equiv(M) ⦄ (d : M → M → F) where
  open import Numeral.Natural
  import      Numeral.Natural.Relation.Order as ℕ

  ConvergesTo : (ℕ → M) → M → Stmt
  ConvergesTo f(L) = ∃{Obj = F₊ → ℕ}(N ↦ ∀{ε : F₊}{n} → (n ℕ.≥ N(ε)) → (d(f(n))(L) < [∃]-witness ε))

  Converging : (ℕ → M) → Stmt
  Converging(f) = ∃(ConvergesTo(f))

  Diverging : (ℕ → M) → Stmt
  Diverging(f) = ∀{L} → ¬(ConvergesTo f(L))

  lim : (f : ℕ → M) → ⦃ Converging(f) ⦄ → M
  lim(f) ⦃ [∃]-intro L ⦄ = L

  Cauchy : (ℕ → M) → Stmt
  Cauchy(f) = ∃{Obj = F₊ → ℕ}(N ↦ ∀{ε : F₊}{a b} → (a ℕ.≥ N(ε)) → (b ℕ.≥ N(ε)) → (d(f(a))(f(b)) < [∃]-witness ε))

  Complete : Stmt
  Complete = Cauchy ⊆ Converging

  Bounded : (ℕ → M) → Stmt
  Bounded(f) = ∃(r ↦ ∃(p ↦ ∀{n} → (d(p)(f(n)) < r)))

  unique-converges-to : ∀{f} → Unique(ConvergesTo(f))

  converging-bounded : Converging ⊆ Bounded

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
