module Miscellaneous.SumOfIntervals where

open import Data.Either
open import Data.List
open import Data.List.Functions
open import Data.Tuple as Tuple
open import Functional
open import Logic.Propositional
open import Lvl
open import Numeral.Natural
import      Numeral.Natural.Function as ℕ
open import Numeral.Natural.Function.Proofs
open import Numeral.Natural.Relation.Order hiding (min)
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type
open import Type.Dependent.Sigma

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

-- An ordered pair of endpoints.
Interval = Σ(ℕ ⨯ ℕ) (uncurry(_≤_))

_‥_ : (a : ℕ) → (b : ℕ) → ⦃ a ≤ b ⦄ → Interval
(a ‥ b) ⦃ ord ⦄ = intro(a , b) ord

min : Interval → ℕ
min(intro(m , _) _) = m

max : Interval → ℕ
max(intro(_ , m) _) = m

-- When the first interval is strictly to the left of the second interval (without intersecting each other).
_<ᵢ_ : Interval → Interval → Type
a <ᵢ b = max a < min b

-- When the first interval is strictly to the right of the second interval (without intersecting each other).
_>ᵢ_ : Interval → Interval → Type
a >ᵢ b = min a > max b

-- When two intervals share end points such that the first one is the left, and the second one is to the right.
Linked : Interval → Interval → Type
Linked(intro(_ , r₁) _) (intro(l₂ , _) _) = r₁ ≡ l₂

-- When two intervals as closed sets have points in common.
-- Examples:
--   ¬ Intersecting(1 ‥ 3) (0 ‥ 0)
--   Intersecting(1 ‥ 3) (0 ‥ 1)
--   Intersecting(1 ‥ 3) (0 ‥ 2)
--   Intersecting(1 ‥ 3) (0 ‥ 3)
--   Intersecting(1 ‥ 3) (0 ‥ 10)
--   Intersecting(1 ‥ 3) (1 ‥ 10)
--   Intersecting(1 ‥ 3) (2 ‥ 10)
--   Intersecting(1 ‥ 3) (3 ‥ 10)
--   ¬ Intersecting(1 ‥ 3) (4 ‥ 10)
--   ¬ Intersecting(1 ‥ 3) (5 ‥ 10)
Intersecting : Interval → Interval → Type
Intersecting(intro(l₁ , r₁) _) (intro(l₂ , r₂) _) = (l₁ ≤ r₂) ∧ (r₁ ≥ l₂)

-- When two intervals have end points in common.
Connected : Interval → Interval → Type
Connected i₁ i₂ = (Linked i₂ i₁) ∨ (Linked i₁ i₂)

-- When two intervals as closed sets have no points in common.
-- Note: This is defined as (_<ᵢ_) being totally ordered for the specific pair of intervals.
Disjoint : Interval → Interval → Type
Disjoint i₁ i₂ = (i₁ <ᵢ i₂) ∨ (i₁ >ᵢ i₂)

-- When the left interval is a subinterval of the right interval.
-- Both intervals are interpreted as closed sets.
_⊆_ : Interval → Interval → Type
i₁ ⊆ i₂ = (min i₁ ≥ min i₂) ∧ (max i₁ ≤ max i₂)

instance
  [<ᵢ]-irreflexivity : Irreflexivity(_<ᵢ_)
  [<ᵢ]-irreflexivity = intro \{ {intro _ b} p → [≤]-to-[≯] b p }

instance
  [<ᵢ]-asymmetry : Asymmetry(_<ᵢ_)
  [<ᵢ]-asymmetry =
    intro \{ {intro(l₁ , r₁) b₁}{intro(l₂ , r₂) b₂} p q → irreflexivity(_<_) $
      l₁ 🝖[ _≤_ ]-[ b₁ ]-sub
      r₁ 🝖[ _<_ ]-[ p ]
      l₂ 🝖[ _≤_ ]-[ b₂ ]-sub
      r₂ 🝖[ _<_ ]-[ q ]-super
      l₁ 🝖[ _≤_ ]-end
    }

instance
  [<ᵢ]-transitivity : Transitivity(_<ᵢ_)
  [<ᵢ]-transitivity =
    intro \{ {intro(l₁ , r₁) b₁}{intro(l₂ , r₂) b₂}{intro(l₃ , r₃) b₃} p q →
      r₁ 🝖[ _<_ ]-[ p ]
      l₂ 🝖[ _≤_ ]-[ b₂ ]-sub
      r₂ 🝖[ _<_ ]-[ q ]-super
      l₃ 🝖[ _≤_ ]-end
    }

instance
  [⊆]-reflexivity : Reflexivity(_⊆_)
  [⊆]-reflexivity = intro ([∧]-intro (reflexivity(_≥_)) (reflexivity(_≤_)))

instance
  [⊆]-transitivity : Transitivity(_⊆_)
  [⊆]-transitivity = intro \([∧]-intro pl pr) ([∧]-intro ql qr) → [∧]-intro (pl 🝖 ql) (pr 🝖 qr)

-- A pair of intervals are not being disjoint and intersect each other at the same time.
disjoint-intersecting-nand : ∀{i₁ i₂} → Disjoint i₁ i₂ → Intersecting i₁ i₂ → ⊥
disjoint-intersecting-nand (Left  dis) (int₁ , int₂) with () ← [≥]-to-[≮] int₂ dis
disjoint-intersecting-nand (Right dis) (int₁ , int₂) with () ← [≥]-to-[≮] int₁ dis

-- A pair of intervals are either disjoint or intersect each other.
disjoint-or-intersecting : ∀{i₁ i₂} → (Disjoint i₁ i₂ ‖ Intersecting i₁ i₂)
disjoint-or-intersecting i₁@{intro(l₁ , r₁) p₁} i₂@{intro(l₂ , r₂) p₂} with [<]-trichotomy {r₁}{l₂} | [<]-trichotomy {l₁}{r₂}
... | Left(Left  p) | Left(Left  q) = Left(Left p) -- [i₁] [i₂]
... | Right      p  | Right      q  = Left(Right q) -- [i₂] [i₁]
... | Left(Right p) | Left(Left  q) = Right([∧]-intro (sub₂(_<_)(_≤_) q) (sub₂(_≡_)(_≥_) p)) -- [i₁][i₂]
... | Right      p  | Left(Right q) = Right([∧]-intro (sub₂(_≡_)(_≤_) q) (sub₂(_<_)(_≤_) p)) -- [i₂][i₁]
... | Left(Right p) | Left(Right q) = Right([∧]-intro (sub₂(_≡_)(_≤_) q) (sub₂(_≡_)(_≥_) p)) -- i₁ = i₂
... | Right      p  | Left(Left  q) = Right([∧]-intro (sub₂(_<_)(_≤_) q) (sub₂(_<_)(_≤_) p)) -- [i₂ [ ] i₁] or [i₁ [ ] i₂]
... | Left(Left  p) | Left(Right q) with () ← irreflexivity(_<_) $
  r₁ 🝖[ _<_ ]-[ p ]-super
  l₂ 🝖[ _≤_ ]-[ p₂ ]
  r₂ 🝖[ _≡_ ]-[ symmetry(_≡_) q ]-sub
  l₁ 🝖[ _≤_ ]-[ p₁ ]
  r₁ 🝖[ _≤_ ]-end
... | Left(Left  p) | Right      q  with () ← irreflexivity(_<_) $
  r₁ 🝖[ _<_ ]-[ p ]-super
  l₂ 🝖[ _≤_ ]-[ p₂ ]
  r₂ 🝖[ _<_ ]-[ q ]-sub
  l₁ 🝖[ _≤_ ]-[ p₁ ]
  r₁ 🝖[ _≤_ ]-end
... | Left(Right p) | Right      q  with () ← irreflexivity(_<_) $
  l₁ 🝖[ _≤_ ]-[ p₁ ]-sub
  r₁ 🝖[ _≡_ ]-[ p ]-sub
  l₂ 🝖[ _≤_ ]-[ p₂ ]-sub
  r₂ 🝖[ _<_ ]-[ q ]-super
  l₁ 🝖[ _≤_ ]-end

-- Merge two intersecting intervals.
merge : (i₁ : Interval) → (i₂ : Interval) → ⦃ Intersecting i₁ i₂ ⦄ → Interval
merge i₁@(intro(l₁ , r₁) b₁) i₂@(intro(l₂ , r₂) b₂) ⦃ int₁ , int₂ ⦄ =
  let
    l₁minr = [↔]-to-[→] [≤]-conjunction-min ([∧]-intro b₁ int₁)
    l₂minr = [↔]-to-[→] [≤]-conjunction-min ([∧]-intro int₂ b₂)
  in intro(ℕ.min l₁ l₂ , ℕ.max r₁ r₂) $
    ℕ.min l₁ l₂ 🝖[ _≤_ ]-[ min-order-max ]
    ℕ.max l₁ l₂ 🝖[ _≤_ ]-[ [↔]-to-[→] [≤]-conjunction-max ([∧]-intro l₁minr l₂minr) ]
    ℕ.min r₁ r₂ 🝖[ _≤_ ]-[ min-order-max ]
    ℕ.max r₁ r₂ 🝖-end

open import Data.List.Relation.Pairwise
open import Data.List.Relation.Pairwise.Proofs
open import Type.Dependent.Functions

{- TODO
insertSorted : Interval → Σ(List(Interval)) (AdjacentlyPairwise(_<ᵢ_)) → Σ(List(Interval)) (AdjacentlyPairwise(_<ᵢ_))
insertSorted i (intro ∅           empty)       = intro (i ⊰ ∅) single
insertSorted i (intro (x ⊰ ∅)     single)      with disjoint-or-intersecting{i}{x}
... | Left(Left  ord) = intro(i ⊰ x ⊰ ∅) (step ord single)
... | Left(Right ord) = intro(x ⊰ i ⊰ ∅) (step ord single)
... | Right int       = intro(merge i x ⦃ int ⦄ ⊰ ∅) single
insertSorted i (intro (x ⊰ l@(y ⊰ l₂)) P@(step xy p)) with disjoint-or-intersecting{i}{x} | insertSorted i (intro l p)
... | Left(Left  ord) | _    = intro(i ⊰ x ⊰ l) (step ord (step xy p))
... | Left(Right ord) | prev = [Σ]-apply prev (x ⊰_) {!!} -- (\{ {∅} P → {!!} ; {X ⊰ L} P → step {!!} {!!} }) prev -- AdjacentlyPairwise-prepend {!step xy p!}
... | Right int       | _    = intro(merge i x ⦃ int ⦄ ⊰ ∅) single

open import Data.List.Functions
sort : List(Interval) → Σ(List(Interval)) (AdjacentlyPairwise(_<ᵢ_))
sort = foldᵣ insertSorted (intro ∅ empty)
-}

-- Examples:
--   insertDisjointSorted (4 ‥ 4) [(1 ‥ 3) , (5 ‥ 10) , (11 ‥ 11) , (14 ‥ 15)] = [(1 ‥ 3) , (4 ‥ 4) , (5 ‥ 10) , (11 ‥ 11) , (14 ‥ 15)]
--   insertDisjointSorted (3 ‥ 4) [(1 ‥ 3) , (5 ‥ 10) , (11 ‥ 11) , (14 ‥ 15)] = [(1 ‥ 4) , (5 ‥ 10) , (11 ‥ 11) , (14 ‥ 15)]
--   insertDisjointSorted (2 ‥ 4) [(1 ‥ 3) , (5 ‥ 10) , (11 ‥ 11) , (14 ‥ 15)] = [(1 ‥ 4) , (5 ‥ 10) , (11 ‥ 11) , (14 ‥ 15)]
--   insertDisjointSorted (1 ‥ 4) [(1 ‥ 3) , (5 ‥ 10) , (11 ‥ 11) , (14 ‥ 15)] = [(1 ‥ 4) , (5 ‥ 10) , (11 ‥ 11) , (14 ‥ 15)]
--   insertDisjointSorted (0 ‥ 4) [(1 ‥ 3) , (5 ‥ 10) , (11 ‥ 11) , (14 ‥ 15)] = [(0 ‥ 4) , (5 ‥ 10) , (11 ‥ 11) , (14 ‥ 15)]
--   insertDisjointSorted (0 ‥ 12) [(1 ‥ 3) , (5 ‥ 10) , (11 ‥ 11) , (14 ‥ 15)] = [(0 ‥ 12) , (14 ‥ 15)]
insertDisjointSorted : Interval → List(Interval) → List(Interval)
insertDisjointSorted i ∅       = singleton i
insertDisjointSorted i (x ⊰ l) with disjoint-or-intersecting{i}{x}
... | Left(Left  ord) = i ⊰ x ⊰ l
... | Left(Right ord) = x ⊰ insertDisjointSorted i l
... | Right int       = insertDisjointSorted (merge i x ⦃ int ⦄) l

module _
  {ℓ}
  (P : Interval → List(Interval) → List(Interval) → Type{ℓ})
  (pe : ∀{i} → P i ∅ (singleton i))
  (pl : ∀{i x}{l} → (i <ᵢ x) → P i (x ⊰ l) (i ⊰ x ⊰ l))
  (pg : ∀{i x}{l L} → (i >ᵢ x) → P i l L → P i (x ⊰ l) (x ⊰ L))
  (pi : ∀{i x}{l L} → ⦃ int : Intersecting i x ⦄ → P(merge i x) l L → P i (x ⊰ l) L)
  where

  insertDisjointSorted-intro : ∀{i}{l} → P i l (insertDisjointSorted i l)
  insertDisjointSorted-intro{i}{∅} = pe
  insertDisjointSorted-intro{i}{x ⊰ l} with disjoint-or-intersecting{i}{x}
  ... | Left(Left  ord) = pl ord
  ... | Left(Right ord) = pg ord (insertDisjointSorted-intro{i}{l})
  ... | Right int       = pi ⦃ int ⦄ (insertDisjointSorted-intro{merge i x ⦃ int ⦄}{l})

module _
  {ℓ}
  (P : Interval → List(Interval) → List(Interval) → Type{ℓ})
  (pe : ∀{i} → P i ∅ (singleton i))
  (pl : ∀{i x}{l} → (i <ᵢ x) → P i (x ⊰ l) (i ⊰ x ⊰ l))
  (pg : ∀{i x}{l} → (i >ᵢ x) → P i l (insertDisjointSorted i l) → P i (x ⊰ l) (x ⊰ insertDisjointSorted i l))
  (pi : ∀{i x}{l} → ⦃ int : Intersecting i x ⦄ → P(merge i x) l (insertDisjointSorted (merge i x) l) → P i (x ⊰ l) (insertDisjointSorted (merge i x) l))
  where

  insertDisjointSorted-intro-specific : ∀{i}{l} → P i l (insertDisjointSorted i l)
  insertDisjointSorted-intro-specific{i}{∅} = pe
  insertDisjointSorted-intro-specific{i}{x ⊰ l} with disjoint-or-intersecting{i}{x}
  ... | Left(Left  ord) = pl ord
  ... | Left(Right ord) = pg ord (insertDisjointSorted-intro-specific{i}{l})
  ... | Right int       = pi{i}{x}{l} ⦃ int ⦄ (insertDisjointSorted-intro-specific{merge i x ⦃ int ⦄}{l})

open import Data.List.Relation.Quantification

-- The intervals to be merged are subintervals of the resulting merged interval.
merge-sub : ∀{i₁ i₂} ⦃ int : Intersecting i₁ i₂ ⦄ → (i₁ ⊆ merge i₁ i₂) ∧ (i₂ ⊆ merge i₁ i₂)
merge-sub{i₁}{i₂} ⦃ int ⦄ = [∧]-intro
  ([∧]-intro ([∧]-elimₗ min-order) ([∧]-elimₗ max-order))
  ([∧]-intro ([∧]-elimᵣ min-order) ([∧]-elimᵣ max-order))

open import Data.List.Relation.Quantification.Existential.Proofs
open import Structure.Function
import      Structure.Relator.Names as Names

-- The interval inserted into a list is a subinterval of one of the intervals in the resulting list.
insertDisjointSorted-inserts : ∀{i l} → ExistsElement(i ⊆_) (insertDisjointSorted i l)
insertDisjointSorted-inserts{i}{l} = insertDisjointSorted-intro(\i l L → ExistsElement (i ⊆_) L)
  (\{i} → • reflexivity(_⊆_) {i})
  (\{i} _ → • reflexivity(_⊆_) {i})
  (\_ → ⊰_)
  (\{j}{x}{_}{L} p → compatible₁(Names.Sub₁)(_→ᶠ_) (Functional.swap(ExistsElement) L) (\{y} → transitivity(_⊆_) {j}{merge j x}{y} ([∧]-elimₗ(merge-sub{j}{x}))) p)
  {i}
  {l}

open import Data.List.Equiv.Id
open import Data.List.Proofs
open import Data.List.Relation.Quantification.Universal.Functions
open import Data.List.Relation.Quantification.Universal.Proofs
open import Logic.Propositional.Equiv
open import Structure.Operator.Properties
open import Structure.Relator

open import Data
open import Data.Option
import      Data.Option.Functions as Option

private variable A B : Type{ℓ}
and-absorberₗ : ∀{o : Option(B)} → (None{T = A} Option.Different.and o ≡ None)
and-absorberₗ {o = None}   = [≡]-intro
and-absorberₗ {o = Some _} = [≡]-intro

and-absorberᵣ : ∀{o : Option(A)} → (o Option.Different.and None{T = B} ≡ None)
and-absorberᵣ {o = None}   = [≡]-intro
and-absorberᵣ {o = Some _} = [≡]-intro

{- TODO: Remove? Probably not necessary
test3 : ∀{_▫_ : T → T → Type{ℓ}} ⦃ trans : Transitivity(_▫_) ⦄ {l₁ l₂} → Option.partialMap Unit (Tuple.uncurry(_▫_)) ((last l₁) Option.Different.and (first l₂)) → ∀ₗᵢₛₜ(l₂) (∀ₗᵢₛₜ(l₁) ∘ (_▫_))
test3 {l₁ = ∅}       {∅}       p = ∅
test3 {l₁ = ∅}       {x₂ ⊰ l₂} p = ∅ ⊰ test3 {l₁ = ∅} {l₂} (substitute₁ₗ(Option.partialMap Unit (uncurry(_))) (and-absorberₗ{A = Type.of x₂}{o =  first l₂}) <>)
test3 {l₁ = x₁ ⊰ l₁} {∅}       p = ∅
test3 {l₁ = x₁ ⊰ l₁} {x₂ ⊰ l₂} p = {!!}

test2 : ∀{_▫_ : T → T → Type{ℓ}}{l₁ l₂} → AdjacentlyPairwise(_▫_)(l₁ ++ l₂) ↔ (AllElements(\x₁ → AllElements(\x₂ → x₁ ▫ x₂) l₂) l₁ ∧ AdjacentlyPairwise(_▫_)(l₁) ∧ AdjacentlyPairwise(_▫_)(l₂))
test2{_▫_ = _▫_} = [↔]-intro {!!} {!!} where
  L : ∀{l₁ l₂} → AllElements(\x₁ → AllElements(\x₂ → x₁ ▫ x₂) l₂) l₁ → AdjacentlyPairwise(_▫_)(l₁) → AdjacentlyPairwise(_▫_)(l₂) → AdjacentlyPairwise(_▫_)(l₁ ++ l₂)
  L po              empty       p2 = p2
  L (po ⊰ ∅)        single      p2 = AdjacentlyPairwise-prepend po p2
  L {l₁ = _ ⊰ _ ⊰ l₁} (ax ⊰ ay ⊰ po₂) (step p p1) p2 = AdjacentlyPairwise-prepend (p ⊰ AllElements-[++] {l₁ = l₁} (OrderedPairwise-head {_▫_ = _▫_} (AdjacentlyPairwise-to-OrderedPairwise ⦃ {!!} ⦄ {!!})) ax) (L (ay ⊰ po₂) p1 p2)
  -- {l₁ = l₁} (OrderedPairwise-head{_▫_ = _▫_} (AdjacentlyPairwise-to-OrderedPairwise ⦃ {!!} ⦄ {!!}))
  -- step p (AdjacentlyPairwise-prepend (OrderedPairwise-head{_▫_ = _▫_} {!!}) (L po₂ (AdjacentlyPairwise-tail p1) p2))

  R : ∀{l₁ l₂} → AdjacentlyPairwise(_▫_)(l₁ ++ l₂) ← (AllElements(\x₁ → AllElements(\x₂ → x₁ ▫ x₂) l₂) l₁ ∧ AdjacentlyPairwise(_▫_)(l₁) ∧ AdjacentlyPairwise(_▫_)(l₂))

test : ∀{i}{l₁ l₂} → AllElements(i >ᵢ_) l₁ → AdjacentlyPairwise(_<ᵢ_) (l₁ ++ l₂) → AdjacentlyPairwise(_<ᵢ_) (l₁ ++ insertDisjointSorted i l₂)
test{i}{l₁}{l₂} = insertDisjointSorted-intro(\i l₂ L → ∀{l₁} → AllElements(i >ᵢ_) l₁ → AdjacentlyPairwise(_<ᵢ_) (l₁ ++ l₂) → AdjacentlyPairwise(_<ᵢ_) (l₁ ++ L))
  (\{x}{l} ix px →
    [↔]-to-[←] (test2{l₁ = l}{l₂ = singleton x})
    $ [∧]-intro ([∧]-intro (AllElements-swap-nested (ix ⊰ ∅)) (substitute₁ᵣ(AdjacentlyPairwise(_<ᵢ_)) (identityᵣ(_++_)(∅)) px)) single
  )
  (\ix iy pyx → {!!}) -- step iy (step ix (AdjacentlyPairwise-tail pyx)))
  (\{i}{x}{l₂}{L} ix pl₂pL {l₁} ail₁ pl₁l₂ →
    substitute₁ᵣ(AdjacentlyPairwise(_<ᵢ_)) ([++]-middle-prepend-postpend{x = x}{l₁}{L})
    $ pl₂pL{postpend x l₁} (AllElements-postpend ix ail₁)
    $ substitute₁ₗ(AdjacentlyPairwise(_<ᵢ_)) ([++]-middle-prepend-postpend{x = x}{l₁}{l₂})
    $ pl₁l₂
  )
  (\{i}{x}{l₂}{L} pl₂pL {l₁} ail₁ pl₁l₂ → pl₂pL{l₁} {!ail₁!} {!!})
  {i}
  {l₂}
  {l₁}

open import Data.Option.Quantifiers

last-of-postpend : ∀{x : T}{l} → last(postpend x l) ≡ Some x
last-of-postpend {l = ∅} = [≡]-intro
last-of-postpend {l = prepend x l} = {!last-of-postpend{l = l}!}

test' : ∀{i}{l₁ l₂} → ∀ₒₚₜ(last l₁) (i >ᵢ_) → AdjacentlyPairwise(_<ᵢ_) (l₁ ++ l₂) → AdjacentlyPairwise(_<ᵢ_) (l₁ ++ insertDisjointSorted i l₂)
test'{i}{l₁}{l₂} = insertDisjointSorted-intro(\i l₂ L → ∀{l₁} → ∀ₒₚₜ(last l₁) (i >ᵢ_) → AdjacentlyPairwise(_<ᵢ_) (l₁ ++ l₂) → AdjacentlyPairwise(_<ᵢ_) (l₁ ++ L))
  (\{x}{l} ix px →
    {!!}
  )
  (\ix iy pyx → {!!})
  (\{i}{x}{l₂}{L} ix pl₂pL {l₁} ail₁ pl₁l₂ →
    substitute₁ᵣ(AdjacentlyPairwise(_<ᵢ_)) ([++]-middle-prepend-postpend{x = x}{l₁}{L})
    $ pl₂pL{postpend x l₁} {!!}
    $ substitute₁ₗ(AdjacentlyPairwise(_<ᵢ_)) ([++]-middle-prepend-postpend{x = x}{l₁}{l₂})
    $ pl₁l₂
  )
  (\{i}{x}{l₂}{L} pl₂pL {l₁} ail₁ pl₁l₂ → pl₂pL{l₁} {!ail₁!} {!!})
  {i}
  {l₂}
  {l₁}
-}

aaaaaaaa : ∀{x y z} ⦃ inter : Intersecting x y ⦄ → (x >ᵢ z) → (y >ᵢ z) → (merge x y >ᵢ z)
aaaaaaaa xz yz = [↔]-to-[→] [≤]-conjunction-min ([∧]-intro xz yz)

test'' : ∀{i x}{l} → (i >ᵢ x) → AdjacentlyPairwise(_<ᵢ_) (x ⊰ l) → AdjacentlyPairwise(_<ᵢ_) (x ⊰ insertDisjointSorted i l)
test''{i}{l₁}{l₂} = insertDisjointSorted-intro(\i l L → ∀{x} → (i >ᵢ x) → AdjacentlyPairwise(_<ᵢ_) (x ⊰ l) → AdjacentlyPairwise(_<ᵢ_) (x ⊰ L))
  (\{i}{x} ix _ → step ix single)
  (\{ {i}{x}{l} ix {y} yi (step yx axl) → step yi (step ix axl) })
  (\{ {i}{x}{l}{L} xi prev {y} yi (step yx axl) → step yx (prev xi axl) })
  (\{
    {i}{x}{∅}    {L} prev {y} yi (step yx axl)           → prev(aaaaaaaa{i}{x}{y} yi yx) single ;
    {i}{x}{a ⊰ l}{L} prev {y} yi (step yx (step xa aal)) → prev(aaaaaaaa{i}{x}{y} yi yx) (AdjacentlyPairwise-prepend-first (transitivity(_<ᵢ_) {y}{x}{a} yx xa) aal)
  })

{-
open import Data.Option.Quantifiers

aaaa : ∀{i x}{l} → (i >ᵢ x) → ∀ₒₚₜ(first l) (_<ᵢ_ x) → ∀ₒₚₜ(first(insertDisjointSorted i l)) (_<ᵢ_ x)
aaaa {i}{x}{l} = insertDisjointSorted-intro(\i l L → (∀ₒₚₜ(first l) \a → ∀ₒₚₜ(first L) \b → a ⊆ b) → ∀{x} → (i >ᵢ x) → ∀ₒₚₜ(first l) (_<ᵢ_ x) → ∀ₒₚₜ(first L) (_<ᵢ_ x))
  -- const
  -- (const const)
  -- (const(const(const id)))
  {-(\{
    -- {i}{y}{l₁} ⦃ int ⦄ prev {x} ix yx → [⊥]-elim (disjoint-intersecting-nand{i}{y} ([∨]-introᵣ ((transitivity(_<ᵢ_) {y}{x}{i} {!yx!} ix))) int)
    {i}{y}{∅}      ⦃ int ⦄ prev {x} ix yx → prev{x} {!!} <> ;
    {i}{y}{a ⊰ l₁} ⦃ int ⦄ prev {x} ix yx → prev{x} {!!} {!!}
  })-}
  {!!}
  {!!}
  {!!}
  (\{i}{y}{l₁} ⦃ int ⦄ prev sub {x} ix yx → {!!})
  {i}
  {l}
  {!!}
  {x}
-}

-- An ordered list of intervals is still ordered after insertion.
insertDisjointSorted-preserve-order : ∀{i}{l} → AdjacentlyPairwise(_<ᵢ_) l → AdjacentlyPairwise(_<ᵢ_) (insertDisjointSorted i l)
insertDisjointSorted-preserve-order{i}{l} = insertDisjointSorted-intro-specific(\i l L → AdjacentlyPairwise(_<ᵢ_) l → AdjacentlyPairwise(_<ᵢ_) L)
  (\_ → single)
  step
  (\{i}{x}{l} ix plpL pxl →
    -- AdjacentlyPairwise-prepend-first {!AdjacentlyPairwise-head pxl!} (plpL(AdjacentlyPairwise-tail pxl))
    -- test'' ix pxl
    AdjacentlyPairwise-prepend-first (AdjacentlyPairwise-head(test'' ix pxl)) (plpL(AdjacentlyPairwise-tail pxl))
    -- AdjacentlyPairwise-prepend (OrderedPairwise-head (AdjacentlyPairwise-to-OrderedPairwise (test''{i}{x}{l} ix pxl))) (plpL pl)
  )
  (\{i}{x}{l} plpL pxl → plpL (AdjacentlyPairwise-tail pxl))
  {i}
  {l}




-- (f : A → Option(B)) → (∀{x} → P(x) → IsTrue(isSome(f(x)))) → ((x : A) → P(x) → B)

{-
-- An ordered pair of endpoints.
Interval = Σ(ℕ ⨯ ℕ) (uncurry(_≤_))

min : Interval → ℕ
min(intro(m , _) _) = m

max : Interval → ℕ
max(intro(_ , m) _) = m

-- When the first interval is strictly to the left of the second interval (without intersecting each other).
_<ᵢ_ : Interval → Interval → Type
intro(_ , r₁) _ <ᵢ intro(l₂ , _) _ = r₁ < l₂

-- When the first interval is strictly to the right of the second interval (without intersecting each other).
_>ᵢ_ : Interval → Interval → Type
intro(_ , r₁) _ >ᵢ intro(l₂ , _) _ = r₁ > l₂ -- TODO: Bad situations: [i₂ [i₁]] , [i₁ [i₂]]. These are overlapping, so this is an incorrect definition, which makes Disjoint incorrect. The definition here should be (l₁ > r₂).

-- When two intervals share end points such that the first one is the left, and the second one is to the right.
Linked : Interval → Interval → Type
Linked(intro(_ , r₁) _) (intro(l₂ , _) _) = r₁ ≡ l₂

-- When two intervals have points in common.
Intersects : Interval → Interval → Type
Intersects(intro(l₁ , r₁) _) (intro(l₂ , r₂) _) = (l₁ ≤ r₂) ∧ (r₁ ≥ l₂)

-- When two intervals have end points in common.
Connected : Interval → Interval → Type
Connected i₁ i₂ = (Linked i₂ i₁) ‖ (Linked i₁ i₂)

-- When two intervals have no points in common.
Disjoint : Interval → Interval → Type
Disjoint i₁ i₂ = (i₁ <ᵢ i₂) ‖ (i₁ >ᵢ i₂)

_⊆_ : Interval → Interval → Type
i₁ ⊆ i₂ = (min i₁ ≥ min i₂) ∧ (max i₁ ≤ max i₂)

-- \(intro(_ , r₁) _ , intro()) → 
-- List(ℕ ⨯ ℕ)

-- Two intervals are either disjoint or intersect.
disjoint-or-intersecting : ∀{i₁ i₂} → (Disjoint i₁ i₂ ‖ Intersects i₁ i₂)
disjoint-or-intersecting i₁@{intro(l₁ , r₁) p₁} i₂@{intro(l₂ , r₂) p₂} with [<]-trichotomy {r₁}{l₂} | [<]-trichotomy {l₁}{r₂}
... | Left(Left  p) | Left(Left  q) = Left(Left p) -- [i₁] [i₂]
... | Left(Right p) | Left(Left  q) = Right([∧]-intro (sub₂(_<_)(_≤_) q) (sub₂(_≡_)(_≥_) p)) -- [i₁][i₂]
... | Left(Right p) | Left(Right q) = Right([∧]-intro (sub₂(_≡_)(_≤_) q) (sub₂(_≡_)(_≥_) p)) -- i₁ = i₂
... | Right      p  | Left(Right q) = Right([∧]-intro (sub₂(_≡_)(_≤_) q) (sub₂(_<_)(_≤_) p)) -- [i₂][i₁]
... | Right      p  | Right      q  = Left(Right p) -- [i₂] [i₁]
... | Right      p  | Left(Left  q) = Right([∧]-intro (sub₂(_<_)(_≤_) q) (sub₂(_<_)(_≤_) p)) -- [i₂ [ ] i₁] or [i₁ [ ] i₂]
... | Left(Left  p) | Left(Right q) with () ← irreflexivity(_<_) $
  r₁ 🝖[ _<_ ]-[ p ]-super
  l₂ 🝖[ _≤_ ]-[ p₂ ]
  r₂ 🝖[ _≡_ ]-[ symmetry(_≡_) q ]-sub
  l₁ 🝖[ _≤_ ]-[ p₁ ]
  r₁ 🝖[ _≤_ ]-end
... | Left(Left  p) | Right      q  with () ← irreflexivity(_<_) $
  r₁ 🝖[ _<_ ]-[ p ]-super
  l₂ 🝖[ _≤_ ]-[ p₂ ]
  r₂ 🝖[ _<_ ]-[ q ]-sub
  l₁ 🝖[ _≤_ ]-[ p₁ ]
  r₁ 🝖[ _≤_ ]-end
... | Left(Right p) | Right      q  with () ← irreflexivity(_<_) $
  l₁ 🝖[ _≤_ ]-[ p₁ ]-sub
  r₁ 🝖[ _≡_ ]-[ p ]-sub
  l₂ 🝖[ _≤_ ]-[ p₂ ]-sub
  r₂ 🝖[ _<_ ]-[ q ]-super
  l₁ 🝖[ _≤_ ]-end

merge : (i₁ : Interval) → (i₂ : Interval) → ⦃ Intersects i₁ i₂ ⦄ → Interval
merge = {!!}
-}
