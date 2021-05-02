module Numeral.Finite.LinearSearch where -- TODO: Maybe move to Numeral.CoordinateVector.LinearSearch

open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.List
import      Data.List.Functions as List
open import Data.Option
import      Data.Option.Functions as Option
open import Functional
open import Logic
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Natural
open import Structure.Relator.Ordering

private variable n : ℕ
private variable i j min max : 𝕟(n)
private variable f : 𝕟(n) → Bool

-- Finds the maximal argument satisfying the given decidable predicate by searching linearly.
-- Examples:
--   findMax{5}   (10 ∣?_) = None
--   findMax{10}  (10 ∣?_) = None
--   findMax{20}  (10 ∣?_) = Some 10
--   findMax{21}  (10 ∣?_) = Some 20
--   findMax{22}  (10 ∣?_) = Some 20
--   findMax{100} (10 ∣?_) = Some 90
--   findMax{102} (10 ∣?_) = Some 100
-- Alternative implementation: findMax f = Option.map Wrapping.[−]_ (findMin(f ∘ Wrapping.[−]_))
findMax : (𝕟(n) → Bool) → Option(𝕟(n))
findMax {𝟎}    f = None
findMax {𝐒(n)} f with f(maximum)
findMax {𝐒(n)} f | 𝑇 = Some maximum
findMax {𝐒(n)} f | 𝐹 = Option.map bound-𝐒 (findMax{n} (f ∘ bound-𝐒))

-- Finds the minimal argument satisfying the given decidable predicate by searching linearly.
-- Examples:
--   findMin{5}   (10 ∣?_) = None
--   findMin{10}  (10 ∣?_) = None
--   findMin{20}  (10 ∣?_) = Some 10
--   findMin{21}  (10 ∣?_) = Some 10
--   findMin{22}  (10 ∣?_) = Some 10
--   findMin{100} (10 ∣?_) = Some 10
--   findMax{102} (10 ∣?_) = Some 10
findMin : (𝕟(n) → Bool) → Option(𝕟(n))
findMin{𝟎}    f = None
findMin{𝐒(n)} f with f(𝟎)
findMin{𝐒(n)} f | 𝑇 = Some 𝟎
findMin{𝐒(n)} f | 𝐹 = Option.map 𝐒 (findMin{n} (f ∘ 𝐒))

-- Finds all arguments satisfying the given decidable predicate by searching linearly.
-- Examples:
--   findAll{10} (2 ∣?_) = [0,2,4,6,8]
findAll : (𝕟(n) → Bool) → List(𝕟(n))
findAll{𝟎}    f = ∅
findAll{𝐒(n)} f = (if f(𝟎) then (𝟎 ⊰_) else id) (List.map 𝐒 (findAll{n} (f ∘ 𝐒)))

{-
open import Data
open import Numeral.Finite.Oper
open import Syntax.Number
findMax' : (𝕟(n) → Bool) → Option(𝕟(n))
findMax' f = Option.map (Wrapping.[−]_) (findMin(f ∘ Wrapping.[−]_))
test : ∀{x y : 𝕟(n)} → (x Wrapping.[−] (x Wrapping.[−] y) ≡ y)
-}

open import Data
open import Data.Boolean.Stmt.Proofs
open import Data.List.Relation.Membership using (_∈_)
open import Data.List.Relation.Membership.Proofs
open import Data.List.Relation.Pairwise
open import Data.List.Relation.Pairwise.Proofs
open import Data.List.Relation.Quantification
open import Data.List.Relation.Quantification.Proofs
open import Data.List.Sorting
open import Data.Option.Equiv.Id
open import Lang.Inspect
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Finite.Oper.Comparisons.Proofs
open import Numeral.Finite.Proofs
open import Numeral.Finite.Relation.Order as 𝕟 using (_≤_ ; _>_ ; _<_ ; [≤]-minimum ; [≤]-maximum)
import      Numeral.Natural.Relation.Order as ℕ
open import Numeral.Natural.Relation.Order.Proofs as ℕ
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Structure.Relator
open import Type.Properties.Decidable
open import Type.Properties.Decidable.Proofs

{-
open import Syntax.Number
test : 𝕟(5) → Bool
test 𝟎 = 𝐹
test (𝐒 𝟎) = 𝐹
test (𝐒 (𝐒 𝟎)) = 𝑇
test (𝐒 (𝐒 (𝐒 𝟎))) = 𝐹
test (𝐒 (𝐒 (𝐒 (𝐒 𝟎)))) = 𝐹
test2 : 𝕟(1) → Bool
test2 𝟎 = 𝑇
test3 : findMax test2 ≡ Some 0
test3 = [≡]-intro
tst4 = {!Option.map bound-𝐒 (findMax (test ∘ bound-𝐒))!}
-}

findMax-None-correctness : (findMax f ≡ None) ↔ (∀{i} → IsFalse(f(i)))
findMax-None-correctness = [↔]-intro l r where
  l : (findMax f ≡ None) ← (∀{i} → IsFalse(f(i)))
  l {𝟎} {f} p = [≡]-intro
  l {𝐒 n} {f} p with f(maximum) | inspect f(maximum)
  ... | 𝑇 | intro fmax with () ← disjointness p ([↔]-to-[←] IsTrue.is-𝑇 fmax)
  ... | 𝐹 | intro fmax = congruence₁(Option.map bound-𝐒) (l p)

  r-result : IsFalse(f(maximum)) → (∀{i : 𝕟(n)} → IsFalse((f ∘ bound-𝐒) i)) → (∀{i : 𝕟(n)} → IsFalse(f(𝐒 i)))
  r-result {𝐒 n}     {f} p q {𝐒 i} = r-result {n}{f ∘ 𝐒} p (\{i} → q{𝐒 i}) {i}
  r-result {𝐒 𝟎}     {f} p q {𝟎}   = p
  r-result {𝐒 (𝐒 n)} {f} p q {𝟎}   = q{𝐒 𝟎}

  r : (findMax f ≡ None) → (∀{i} → IsFalse(f(i)))
  r {𝐒 n}     {f} p {i} with f(maximum) | inspect f(maximum)
  r {𝐒 n}     {f} p {𝐒 i} | 𝐹 | intro fmax = r-result {f = f} ([↔]-to-[←] IsFalse.is-𝐹 fmax) (\{i} → r {n}{f ∘ bound-𝐒} (map-None p) {i}) {i}
  r {𝐒 𝟎}     {f} p {𝟎}   | 𝐹 | intro fmax = [↔]-to-[←] IsFalse.is-𝐹 fmax
  r {𝐒 (𝐒 n)} {f} p {𝟎}   | 𝐹 | intro fmax = r {𝐒 n} {f ∘ bound-𝐒} (map-None p) {𝟎}

findMax-Some-correctness : (findMax f ≡ Some(i)) → IsTrue(f(i))
findMax-Some-correctness {𝐒 n} {f} {i}        eq with f(maximum) | inspect f(maximum)
findMax-Some-correctness {𝐒 n} {f} {.maximum} [≡]-intro | 𝑇 | intro fmax = [↔]-to-[←] IsTrue.is-𝑇 fmax
findMax-Some-correctness {𝐒 n} {f} {i}        eq        | 𝐹 | intro fmax with findMax(f ∘ bound-𝐒) | inspect findMax(f ∘ bound-𝐒)
findMax-Some-correctness {𝐒 n} {f} {.(_)}     [≡]-intro | 𝐹 | intro fmax | Some x | intro p = findMax-Some-correctness {f = f ∘ bound-𝐒} p

findMin-None-correctness : (findMin f ≡ None) ↔ (∀{i} → IsFalse(f(i)))
findMin-None-correctness = [↔]-intro l r where
  l : (findMin f ≡ None) ← (∀{i} → IsFalse(f(i)))
  l {𝟎} {f} p = [≡]-intro
  l {𝐒 n} {f} p with f(𝟎) | inspect f(𝟎)
  ... | 𝑇 | intro f0 with () ← disjointness p ([↔]-to-[←] IsTrue.is-𝑇 f0)
  ... | 𝐹 | intro f0 = congruence₁(Option.map 𝐒) (l p)

  r : (findMin f ≡ None) → (∀{i} → IsFalse(f(i)))
  r {𝐒 n} {f} p {i} with f(𝟎) | inspect f(𝟎)
  r {𝐒 n} {f} p {𝟎}   | 𝐹 | intro f0 = [↔]-to-[←] IsFalse.is-𝐹 f0
  r {𝐒 n} {f} p {𝐒 i} | 𝐹 | intro f0 = r {f = f ∘ 𝐒} (injective(Option.map 𝐒) ⦃ map-injectivity ⦄ p)

findMin-Some-correctness : (findMin f ≡ Some(min)) → IsTrue(f(min))
findMin-Some-correctness {𝐒 n} {f} {min} eq with f(𝟎) | inspect f(𝟎)
findMin-Some-correctness {𝐒 n} {f} {𝟎}     [≡]-intro | 𝑇 | intro f0 = [↔]-to-[←] IsTrue.is-𝑇 f0
findMin-Some-correctness {𝐒 n} {f} {𝟎}     eq        | 𝐹 | intro f0 with findMin{n} (f ∘ 𝐒)
findMin-Some-correctness {𝐒 n} {f} {𝟎}     ()        | 𝐹 | intro f0 | None
findMin-Some-correctness {𝐒 n} {f} {𝟎}     ()        | 𝐹 | intro f0 | Some _
findMin-Some-correctness {𝐒 n} {f} {𝐒 min} eq        | 𝐹 | intro f0 = findMin-Some-correctness {n} {f ∘ 𝐒} {min} (injective(Option.map 𝐒) ⦃ map-injectivity ⦄ eq)

findMin-minimal-true : (findMin f ≡ Some(min)) → IsTrue(f(i)) → (min ≤ i)
findMin-minimal-true {𝐒 n} {f} {min}   {i}   eq        p with f(𝟎) | inspect f(𝟎)
findMin-minimal-true {𝐒 n} {f} {.𝟎}    {i}   [≡]-intro p | 𝑇 | intro f0 = 𝕟.[≤]-minimum {a = i}
findMin-minimal-true {𝐒 n} {f} {𝟎}     {i}   eq        p | 𝐹 | intro f0 with findMin{n} (f ∘ 𝐒)
findMin-minimal-true {𝐒 n} {f} {𝟎}     {i}   ()        p | 𝐹 | intro f0 | None
findMin-minimal-true {𝐒 n} {f} {𝟎}     {i}   ()        p | 𝐹 | intro f0 | Some _
findMin-minimal-true {𝐒 n} {f} {𝐒 min} {𝟎}   eq        p | 𝐹 | intro f0 = disjointness p ([↔]-to-[←] IsFalse.is-𝐹 f0)
findMin-minimal-true {𝐒 n} {f} {𝐒 min} {𝐒 i} eq        p | 𝐹 | intro f0 = findMin-minimal-true {n} {f ∘ 𝐒} {min} {i} (injective(Option.map 𝐒) ⦃ map-injectivity ⦄ eq) p

findMin-minimal-false : (findMin f ≡ Some(min)) → (min > i) → IsFalse(f(i))
findMin-minimal-false {n}{f}{min}{i} eq =
  [↔]-to-[←] false-true-opposites
  ∘ contrapositiveᵣ(findMin-minimal-true{n}{f}{min}{i} eq)
  ∘ [↔]-to-[←] decider-true ∘ substitute₁ₗ(IsTrue) (⋚-elim₃-negation-distribution {x = min}{y = i})

{-
instance
  [≤]-with-[𝐒]-injective : ∀{a b} → Injective(\p → ℕ.[≤]-with-[𝐒] {a}{b} ⦃ p ⦄)
  Injective.proof [≤]-with-[𝐒]-injective [≡]-intro = [≡]-intro

import      Structure.Function.Names as Names
open import Function.Equals
bound-[≤]-injective : ∀{a b} → Injective ⦃ [≡]-equiv ⦄ ⦃ [⊜]-equiv ⦄ (bound-[≤] {a}{b})
bound-[≤]-injective {a}{b} = intro proof where
  proof : Names.Injective ⦃ [≡]-equiv ⦄ ⦃ [⊜]-equiv ⦄ (bound-[≤] {a}{b})
  proof {ℕ.[≤]-minimum} {ℕ.[≤]-minimum} p = [≡]-intro
  proof {ℕ.[≤]-with-[𝐒] ⦃ x ⦄} {ℕ.[≤]-with-[𝐒] ⦃ y ⦄} (intro p) = {!(injective ⦃ ? ⦄ ⦃ ? ⦄ (𝕟.𝐒) ⦃ ? ⦄ {x = bound-[≤] x}{y = bound-[≤] y} p)!}
--Injective.proof bound-[≤]-injective {ℕ.[≤]-minimum} {ℕ.[≤]-minimum} p = [≡]-intro
--Injective.proof bound-[≤]-injective {ℕ.[≤]-with-[𝐒] {y = _} ⦃ x ⦄} {ℕ.[≤]-with-[𝐒] {y = _} ⦃ y ⦄} (intro p) = {!injective(𝐒) ⦃ ? ⦄ p!}
-- injective(𝐒) ⦃ [≤]-with-[𝐒]-injective ⦄

bound-𝐒-injective : Injective(bound-𝐒 {n})
Injective.proof bound-𝐒-injective {𝟎} {𝟎} p = [≡]-intro
Injective.proof bound-𝐒-injective {𝐒 x} {𝐒 y} p = congruence₁(𝐒) (Injective.proof bound-𝐒-injective {x} {y} (injective(𝐒) p))
-}

-- TODO
postulate findMax-maximal-true : (findMax f ≡ Some(max)) → IsTrue(f(i)) → (i ≤ max)
{-findMax-maximal {𝐒 n}{f} eq p with f(maximum) | inspect f(maximum)
findMax-maximal {𝐒 n} {f} {i = i} [≡]-intro p | 𝑇 | intro m = [≤]-maximum {𝐒 n}{i} (reflexivity(ℕ._≤_))
findMax-maximal {𝐒 n} {f} {i = i} eq p | 𝐹 | intro m with findMax{n} (f ∘ bound-𝐒) | inspect (findMax{n}) (f ∘ bound-𝐒)
findMax-maximal {𝐒 n} {f} {i = i} eq p | 𝐹 | intro m | Some x | intro findMax-x = {!findMax-maximal {n} {f ∘ bound-𝐒} {i = ?} !}
-}

{- TODO
test : ∀{i : 𝕟(𝐒(n))} → ¬(maximum{n} < i)
test {𝟎}   {𝟎}   p = p
test {𝐒 n} {𝟎}   p = p
test {𝐒 n} {𝐒 i} p = test {n}{i} p

{-
findMax-maximal2 : (findMax f ≡ Some(max)) → (i > max) → IsFalse(f(i))
findMax-maximal2 {𝐒 n} {f} {max} {i} eq p with f(maximum) | inspect f(maximum)
findMax-maximal2 {𝐒 n} {f} {𝟎} {𝐒 i} eq p | 𝑇 | intro fmax with maximum-0(injective(Some) eq)
findMax-maximal2 {𝐒 .0} {f} {𝟎} {𝐒 ()} eq p | 𝑇 | intro fmax | [≡]-intro
findMax-maximal2 {𝐒 (𝐒 n)} {f} {𝐒 max} {𝐒 i} eq p | 𝑇 | intro fmax with f(bound-𝐒 maximum) | inspect (f ∘ bound-𝐒)(maximum)
findMax-maximal2 {𝐒 (𝐒 n)} {f} {𝐒 .maximum} {𝐒 i} [≡]-intro p | 𝑇 | intro fmax | 𝑇 | intro x with () ← test{n} p
findMax-maximal2 {𝐒 (𝐒 n)} {f} {𝐒 {.(𝐒 n)} .(maximum {n})} {𝐒 {.(𝐒 n)} i} ([≡]-intro {x = .(Some (𝐒 {𝐒 n} (maximum {n})))}) p | 𝑇 | intro fmax | 𝐹 | intro x with () ← test{n} p
findMax-maximal2 {𝐒 n} {f} {𝟎} {𝐒 i} eq p | 𝐹 | intro fmax = {!!}
findMax-maximal2 {𝐒 n} {f} {𝐒 max} {𝐒 i} eq p | 𝐹 | intro fmax = {!!}
-}


test2 : (bound-𝐒 i ≡ 𝟎) → (i ≡ 𝟎)
test2 {i = 𝟎} p = [≡]-intro

findMax-maximal : (findMax f ≡ Some(max)) → IsTrue(f(i)) → (i ≤ max)
findMax-maximal {𝐒 n}{f} eq p with f(maximum) | inspect f(maximum)
findMax-maximal {𝐒 n} {f} {_}{i} [≡]-intro p | 𝑇 | intro fmax = [≤]-maximum {𝐒 n}{i} (reflexivity(ℕ._≤_))
findMax-maximal {𝐒 n} {f} {max} {𝟎} eq p | 𝐹 | intro fmax = [≤]-minimum {a = max}
findMax-maximal {𝐒 (𝐒 n)} {f} {max} {𝐒 i} eq p | 𝐹 | intro fmax with f(bound-𝐒 maximum) | inspect (f ∘ bound-𝐒)(maximum)
findMax-maximal {𝐒 (𝐒 n)} {f} {𝟎} {𝐒 i} eq p | 𝐹 | intro fmax | 𝑇 | intro x = {!maximum-0(test2(injective(Some) eq))!}
findMax-maximal {𝐒 (𝐒 n)} {f} {𝐒 max} {𝐒 i} eq p | 𝐹 | intro fmax | 𝑇 | intro x = {!!}
... | 𝐹 | intro x = {!!}
-- findMax-maximal {f = f ∘ bound-𝐒} {i = i} (injective(Option.map bound-𝐒) ⦃ map-injectivity ⦃ ? ⦄ ⦄ {findMax(f ∘ bound-𝐒)} {Some 𝟎} eq)
{-findMax-maximal {𝐒 n} {f} {max} {i} eq p with f(maximum) | inspect f(maximum)
findMax-maximal {𝐒 n} {f} {.maximum} {i} [≡]-intro p | 𝑇 | intro fmax = [≤]-maximum {𝐒 n}{i}{n = n} (reflexivity(ℕ._≤_))
findMax-maximal {𝐒 n} {f} {max} {i} eq p | 𝐹 | intro fmax with findMax{n} (f ∘ bound-𝐒)
findMax-maximal {𝐒 n} {f} {max} {i} () p | 𝐹 | intro fmax | None
-}
{-findMax-maximal {𝐒 n} {f} {𝟎}     {𝟎}   eq p | 𝐹 | intro fmax | Some x = <>
findMax-maximal {𝐒 n} {f} {𝐒 max} {𝟎}   eq p | 𝐹 | intro fmax | Some x = <>
findMax-maximal {𝐒(𝐒 n)} {f} {𝟎} {𝐒 i} eq p | 𝐹 | intro fmax | Some 𝟎 = {!findMax-maximal!}
findMax-maximal {𝐒 n} {f} {𝐒 max} {𝐒 i} eq p | 𝐹 | intro fmax | Some x = {!!}
-}
{-findMax-maximal {𝐒 n} {f} {.(bound-[≤] ([≤]-successor ([≡]-to-[≤] [≡]-intro)) x)} {𝟎} [≡]-intro p | 𝐹 | intro fmax | Some x = [≤]-minimum {a = bound-𝐒(x)}
findMax-maximal {𝐒 .(𝐒 _)} {f} {.(bound-[≤] ([≤]-successor ([≡]-to-[≤] [≡]-intro)) 𝟎)} {𝐒 i} [≡]-intro p | 𝐹 | intro fmax | Some 𝟎 = {!!}
findMax-maximal {𝐒 .(𝐒 _)} {f} {.(bound-[≤] ([≤]-successor ([≡]-to-[≤] [≡]-intro)) (𝐒 x))} {𝐒 i} [≡]-intro p | 𝐹 | intro fmax | Some (𝐒 x) = {!!}-}
-}

{-
open import Numeral.Finite.Oper
findMax-findMin : findMax f ≡ Option.map Wrapping.[−]_ (findMin(f ∘ Wrapping.[−]_))
findMax-findMin {𝟎} {f} = [≡]-intro
findMax-findMin {𝐒 n} {f} with f(maximum) | inspect f(maximum)
... | 𝑇 | intro fmax = [≡]-intro
... | 𝐹 | intro fmax = {!!}
-}

findAll-correctness : AllElements(IsTrue ∘ f)(findAll f)
findAll-correctness {𝟎}   {f} = ∅
findAll-correctness {𝐒 n} {f} with f(𝟎) | inspect f(𝟎)
... | 𝑇 | intro f0 = ([↔]-to-[←] IsTrue.is-𝑇 f0) ⊰ (AllElements-mapᵣ 𝐒 id (findAll-correctness {n}{f ∘ 𝐒}))
... | 𝐹 | intro _  = AllElements-mapᵣ 𝐒 id (findAll-correctness {n}{f ∘ 𝐒})

findAll-completeness : IsTrue(f(i)) → (i ∈ findAll f)
findAll-completeness {𝐒 n} {f} {i}   p with f(𝟎) | inspect f(𝟎)
findAll-completeness {𝐒 n} {f} {𝟎}   p | 𝑇 | intro _  = • [≡]-intro
findAll-completeness {𝐒 n} {f} {𝐒 i} p | 𝑇 | intro _  = ⊰ [∈]-map (findAll-completeness{n}{f ∘ 𝐒}{i} p)
findAll-completeness {𝐒 n} {f} {𝟎}   p | 𝐹 | intro f0 with () ← disjointness p ([↔]-to-[←] IsFalse.is-𝐹 f0)
findAll-completeness {𝐒 n} {f} {𝐒 i} p | 𝐹 | intro _  = [∈]-map (findAll-completeness {n} {f ∘ 𝐒} {i} p)

findAll-sorted : Sorted(_≤?_)(findAll f)
findAll-sorted {𝟎}      {f} = AdjacentlyPairwise.empty
findAll-sorted {𝐒 𝟎} {f} with f(𝟎) | inspect f(𝟎)
findAll-sorted {𝐒 𝟎} {f} | 𝑇 | intro f0 = AdjacentlyPairwise.single
findAll-sorted {𝐒 𝟎} {f} | 𝐹 | intro f0 = AdjacentlyPairwise.empty
findAll-sorted {𝐒(𝐒 n)} {f} with f(𝟎) | f(𝐒 𝟎) | AdjacentlyPairwise-map {_▫₁_ = IsTrue ∘₂ _≤?_}{f = 𝐒}{_▫₂_ = IsTrue ∘₂ _≤?_} id (findAll-sorted {𝐒 n}{f ∘ 𝐒})
... | 𝑇 | 𝑇 | prev = AdjacentlyPairwise.step ⦃ <> ⦄ ⦃ prev ⦄
... | 𝑇 | 𝐹 | prev = AdjacentlyPairwise-prepend (\{ {𝟎} → <> ; {𝐒 _} → <>}) prev
... | 𝐹 | 𝑇 | prev = prev
... | 𝐹 | 𝐹 | prev = prev
