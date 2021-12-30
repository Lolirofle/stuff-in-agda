open import Logic
open import Logic.Classical
open import Structure.Function.Metric
open import Structure.OrderedField
open import Structure.Setoid
open import Type

module Structure.Function.Metric.Subspace.Proofs
  {ℓF ℓₑF ℓ≤ ℓₘ ℓₑₘ ℓₙ₀}
  {F : Type{ℓF}}
  ⦃ equiv-F : Equiv{ℓₑF}(F) ⦄
  {_+_}{_⋅_}
  {_≤_ : _ → _ → Type{ℓ≤}}
  ⦃ orderedField-F : OrderedField{F = F}{ℓₙ₀ = ℓₙ₀}(_+_)(_⋅_)(_≤_) ⦄
  {M : Type{ℓₘ}} ⦃ equiv-M : Equiv{ℓₑₘ}(M) ⦄
  (d : M → M → F) ⦃ metric : MetricSpace(d) ⦄
  where

open MetricSpace(metric)
open OrderedField(orderedField-F)

import      Lvl
import      Data.Either as Either
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional as Fn
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Logic.Predicate.Theorems
open import Sets.PredicateSet renaming (_≡_ to _≡ₛ_)
open import Structure.Operator.Properties
open import Structure.Operator.Ring.Proofs
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Implication
open import Syntax.Transitivity

private F₊ = ∃(Positive)

module _ where
  private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
  private variable x y z : M

  private variable p p₁ p₂ : M
  private variable E E₁ E₂ E₃ E₄ : PredSet{ℓ}(M)
  private variable Es : PredSet{ℓ₁}(PredSet{ℓ₂}(M))
  private variable r r₁ r₂ : F₊

  open import Structure.Function.Metric.Proofs d ⦃ metric ⦄
  open import Structure.Function.Metric.Subspace d ⦃ metric ⦄

  interior-subspace-sub : Interior(E) ⊆ E
  interior-subspace-sub {x = x} ([∃]-intro y ⦃ p ⦄) = p (neighborhood-contains-center{x}{y})

  isolated-points-subspace-sub : IsolatedPoint(E) ⊆ E
  isolated-points-subspace-sub = [∧]-elimₗ

  subspace-closure-sub : E ⊆ Closure(E)
  subspace-closure-sub = [∨]-introₗ

  [⊆]-with-Interior : (E₁ ⊆ E₂) → (Interior(E₁) ⊆ Interior(E₂))
  [⊆]-with-Interior sub ([∃]-intro r ⦃ p ⦄) = [∃]-intro r ⦃ sub ∘ p ⦄

  [⊆]-with-LimitPoint : (E₁ ⊆ E₂) → (LimitPoint(E₁) ⊆ LimitPoint(E₂))
  [⊆]-with-LimitPoint sub xLpE₁ {r} = overlapping-super id sub (xLpE₁{r})

  -- limit-point-idempotence : LimitPoint(LimitPoint(E)) ≡ₛ LimitPoint(E)
  -- limit-point-idempotence = [↔]-intro (\p {r} → [∃]-map-proof ([∧]-elim \a b → [∧]-intro a \{r2} → [∃]-intro {!!} ⦃ [∧]-intro {!!} b ⦄) (p{r})) {!!}

  neighborhood-interior-is-self : (Interior(Neighborhood(p)(r)) ≡ₛ Neighborhood(p)(r))
  ∃.witness (Tuple.left (neighborhood-interior-is-self {p} {[∃]-intro r} {x}) Nx) = [∃]-intro (r − d(p)(x)) ⦃ intro ([↔]-to-[←] [<]-positive-difference Nx) ⦄
  ∃.proof (Tuple.left (neighborhood-interior-is-self {p} {[∃]-intro r ⦃ _ ⦄} {x}) Nx) {y} Ny =
    d(p)(y)                 🝖[ _≤_ ]-[ triangle-inequality ]-sub
    d(p)(x) + d(x)(y)       🝖[ _<_ ]-[ [<][+]-preserveᵣ Ny ]-super
    d(p)(x) + (r − d(p)(x)) 🝖[ _≡_ ]-[ commutativity(_+_) ]
    (r − d(p)(x)) + d(p)(x) 🝖[ _≡_ ]-[ inverseOperᵣ(_−_)(_+_) ⦃ [−][+]-inverseOperᵣ ⦄ ]
    r 🝖-end
  Tuple.right neighborhood-interior-is-self = interior-subspace-sub

  {-
  limit-points-of-intersection : LimitPoint(E₁ ∩ E₂) ⊇ (LimitPoint(E₁) ∩ LimitPoint(E₂))
  limit-points-of-intersection {x = x} ([∧]-intro xLpE₁ xLpE₂) {r}
    with [∃]-intro p₁ ⦃ [∧]-intro ([∧]-intro a b) pE₁ ⦄ ← xLpE₁{r}
    with [∃]-intro p₂ ⦃ [∧]-intro ([∧]-intro c d) pE₂ ⦄ ← xLpE₂{r}
    = [∃]-intro {!!} ⦃ [∧]-intro ([∧]-intro {!!} {!!}) ([∧]-intro {!!} {!!}) ⦄
  -}

  limit-points-of-union : LimitPoint(E₁ ∪ E₂) ⊇ (LimitPoint(E₁) ∪ LimitPoint(E₂))
  limit-points-of-union{E₁ = E₁}{E₂ = E₂} = [∨]-elim
    (\p {r} → overlapping-super id (\{x} → [⊆]-of-[∪]ₗ {S₁ = E₁}{S₂ = E₂}{x = x}) (p{r}))
    (\p {r} → overlapping-super id (\{x} → [⊆]-of-[∪]ᵣ {S₂ = E₂}{S₁ = E₁}{x = x}) (p{r}))

  interior-idempotence : Interior(Interior E) ≡ₛ Interior E
  interior-idempotence = [↔]-intro left right where
    left : Interior(Interior E) ⊇ Interior E
    left ([∃]-intro r ⦃ intE ⦄) = [∃]-intro r ⦃ [⊆]-with-Interior intE ∘ [↔]-to-[←] (neighborhood-interior-is-self {r = r}) ⦄

    right : Interior(Interior E) ⊆ Interior E
    right ([∃]-intro r ⦃ intIntE ⦄) = [∃]-intro r ⦃ interior-subspace-sub ∘ intIntE ⦄

  closure-membershipᵣ : (p ∈ Closure(E)) → (∀{r} → Overlapping(Neighborhood(p)(r)) (E))
  closure-membershipᵣ {p = p} (Either.Left pE) {r} = [∃]-intro p ⦃ [∧]-intro (neighborhood-contains-center{r = r}) pE ⦄
  closure-membershipᵣ         (Either.Right pLP) {r} = [∃]-map-proof ([∧]-map (punctured-neighborhood-neighborhood-sub{r = r}) id) (pLP{r})

  -- TODO: Only when dense?
  -- isolated-interior-disjoint : Disjoint(IsolatedPoint(E)) (Interior(E))
  -- isolated-interior-disjoint ([∧]-intro ([∧]-intro _ ip) intp) = [∃]-proof ip ([∧]-intro ({!!} , {!!}) {!!})

  isolated-or-limit-closure-point-sub : (IsolatedPoint(E) ∪ LimitPoint(E)) ⊆ Closure(E)
  isolated-or-limit-closure-point-sub ([∨]-introₗ ip) = [∨]-introₗ (isolated-points-subspace-sub ip)
  isolated-or-limit-closure-point-sub ([∨]-introᵣ lp) = [∨]-introᵣ \{x} → lp{x}

  module _ ⦃ classical : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P) ⦄ where
    isolated-limit-disjoint : Disjoint(IsolatedPoint(E)) (LimitPoint(E))
    isolated-limit-disjoint ([∧]-intro ([∧]-intro _ ip) lp) = [⊕]-not-both disjoint-xor-overlapping ([∃]-proof ip) (lp{[∃]-witness ip})

    closure-membership : ⦃ UnaryRelator(E) ⦄ → (p ∈ Closure(E)) ↔ (∀{r} → Overlapping(Neighborhood(p)(r)) (E))
    closure-membership{E = E}{p = p} = [↔]-intro left closure-membershipᵣ where
      left : (p ∈ Closure(E)) ← (∀{r} → Overlapping(Neighborhood(p)(r)) (E))
      left overl = [¬¬]-elim ⦃ classical ⦄ $ \npCl →
        npCl ⇒
        (p ∉ Closure E)                                                   ⇒-[]
        (p ∉ (E ∪ LimitPoint(E)))                                         ⇒-[]
        ¬((p ∈ E) ∨ (p ∈ LimitPoint(E)))                                  ⇒-[ [↔]-to-[→] [¬]-preserves-[∨][∧] ]
        ((p ∉ E) ∧ (p ∉ LimitPoint(E)))                                   ⇒-[ [∧]-map id [¬∀]-to-[∃¬] ]
        ((p ∉ E) ∧ ∃(r ↦ ¬ Overlapping(PuncturedNeighborhood(p)(r)) (E))) ⇒-[ [∧]-map id ([∃]-map-proof (_∘ Overlapping-symmetry)) ]
        ((p ∉ E) ∧ ∃(r ↦ ¬ Overlapping E (PuncturedNeighborhood(p)(r))))  ⇒-[ [∧]-map id ([∃]-map-proof ([¬¬]-elim ∘ contrapositiveᵣ([↔]-to-[→] [⊈]-complement-to-overlapping))) ]
        ((p ∉ E) ∧ ∃(r ↦ E ⊆ ∁(PuncturedNeighborhood(p)(r))))           ⇒-[ ((\([∧]-intro npE ([∃]-intro r ⦃ EPN ⦄)) → let [∃]-intro q ⦃ [∧]-intro dpqr qE ⦄ = overl{r} in EPN qE ([¬¬]-elim ⦃ classical ⦄ (Either.elim ([≥][≢]-to-[>] (NonNegative.proof non-negativity) (contrapositiveᵣ([↔]-to-[→] self-distance) (npE ∘ (pq ↦ substitute₁ᵣ(E) (symmetry(_≡_) pq) qE)))) dpqr ∘ Either.map [¬¬]-elim [¬¬]-elim ∘ [¬]-preserves-[∧][∨]ᵣ ⦃ classical ⦄ ⦃ classical ⦄)))) ]
        ⊥                                                                 ⇒-end
