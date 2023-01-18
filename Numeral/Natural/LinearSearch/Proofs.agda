module Numeral.Natural.LinearSearch.Proofs where

open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Logic
open import Data.Option
import      Data.Option.Functions as Option
open import Data.Option.Equiv.Id
open import Data.Option.Proofs
import      Data.Tuple as Tuple
open import Function.Equals
open import Functional
open import Lang.Inspect
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.LinearSearch
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Proofs
open import Numeral.Natural.Relation.Order hiding (min)
open import Numeral.Natural.Relation.Order.Classical
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator
open import Structure.Operator.Proofs.EquivalentStructure
open import Structure.Operator.Properties
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Implication
open import Syntax.Transitivity
open import Type

private variable a b n i j min max : ℕ
private variable f : ℕ → Bool

-- When findUpperboundedMin returns None for the given arguments, all values of f lesser than the upper bound is false.
findUpperboundedMin-None-correctness : (findUpperboundedMin max f ≡ None) ↔ (∀{i} → (i < max) → IsFalse(f(i)))
findUpperboundedMin-None-correctness = [↔]-intro l r where
  l : (findUpperboundedMin max f ≡ None) ← (∀{i} → (i < max) → IsFalse(f(i)))
  l {𝟎}     {f} p = [≡]-intro
  l {𝐒 max} {f} p with f(𝟎) | inspect f(𝟎)
  ... | 𝑇 | intro f0 with () ← disjointness([↔]-to-[←] IsTrue.is-𝑇 f0) (p{𝟎} (succ _≤_.min))
  ... | 𝐹 | intro f0 = congruence₁(Option.map 𝐒) (l{max}{f ∘ 𝐒} (p ∘ succ))

  r : (findUpperboundedMin max f ≡ None) → (∀{i} → (i < max) → IsFalse(f(i)))
  r {𝐒 max} {f} eq {i}   ord   with f(𝟎) | inspect f(𝟎)
  r {𝐒 max} {f} eq {𝟎}   ord        | 𝐹  | intro f0 = [↔]-to-[←] IsFalse.is-𝐹 f0
  r {𝐒 max} {f} eq {𝐒 i} (succ ord) | 𝐹  | intro f0 = r{max}{f ∘ 𝐒} (injective(Option.map 𝐒) ⦃ map-injectivity ⦄ eq) {i} ord

-- When findUpperboundedMin returns Some for the given arguments, then the number returned gives a value of true for f, is the minimal one, and is lesser than the upper bound.
findUpperboundedMin-Some-correctness : (findUpperboundedMin max f ≡ Some(n)) ↔ (IsTrue(f(n)) ∧ (n < max) ∧ (∀{i} → IsTrue(f(i)) → (n ≤ i)))
findUpperboundedMin-Some-correctness = [↔]-intro l r where
  l : (findUpperboundedMin max f ≡ Some(n)) ← (IsTrue(f(n)) ∧ (n < max) ∧ (∀{i} → IsTrue(f(i)) → (n ≤ i)))
  l {𝐒 max}{f}{n}    ([∧]-intro ([∧]-intro corr range)        minimal) with f(𝟎) | inspect f(𝟎)
  l {𝐒 max}{f}{n}    ([∧]-intro ([∧]-intro corr range)        minimal) | 𝑇 | intro f0 with _≤_.min ← minimal ([↔]-to-[←] IsTrue.is-𝑇 f0) = [≡]-intro
  l {𝐒 max}{f}{𝟎}    ([∧]-intro ([∧]-intro corr range)        minimal) | 𝐹 | intro f0 with () ← disjointness corr ([↔]-to-[←] IsFalse.is-𝐹 f0)
  l {𝐒 max}{f}{𝐒(n)} ([∧]-intro ([∧]-intro corr (succ range)) minimal) | 𝐹 | intro f0 = congruence₁(Option.map 𝐒) (l{max}{f ∘ 𝐒}{n} ([∧]-intro ([∧]-intro corr range) ([≤]-without-[𝐒] ∘ minimal)))

  r : (findUpperboundedMin max f ≡ Some(n)) → (IsTrue(f(n)) ∧ (n < max) ∧ (∀{i} → IsTrue(f(i)) → (n ≤ i)))
  r {𝐒 max} {f} {n}   eq with f(𝟎) | inspect f(𝟎)
  r {𝐒 max} {f} {.𝟎}  [≡]-intro | 𝑇 | intro f0 = [∧]-intro ([∧]-intro ([↔]-to-[←] IsTrue.is-𝑇 f0) (succ _≤_.min)) (const _≤_.min)
  r {𝐒 max} {f} {𝐒 n} eq        | 𝐹 | intro f0 = [∧]-map ([∧]-map id succ) (\{_ {𝟎} f0t → [⊥]-elim (disjointness f0t ([↔]-to-[←] IsFalse.is-𝐹 f0)) ; p {𝐒 i} → succ ∘ p{i} }) (r{max}{f ∘ 𝐒}{n} (injective(Option.map 𝐒) ⦃ map-injectivity ⦄ eq))
  r {𝐒 max} {f} {𝟎}   eq        | 𝐹 | intro f0 = [⊥]-elim (p{findUpperboundedMin max (f ∘ 𝐒)} eq) where
    p : ∀{o} → (Option.map ℕ.𝐒(o) ≡ Some 𝟎) → ⊥
    p {None}   ()
    p {Some _} ()

findBoundedMin-None-correctness : (findBoundedMin min max f ≡ None) ↔ (∀{i} → (min ≤ i < max) → IsFalse(f(i)))
findBoundedMin-None-correctness{min}{max}{f} with [≤]-or-[>] {min}{max}
... | [∨]-introᵣ gt rewrite [↔]-to-[→] [−₀]-when-0 ([≤]-predecessor gt) = [↔]-intro
  (const [≡]-intro)
  (\_ ([∧]-intro pmin pmax) → [⊥]-elim ([≤]-to-[≯] pmin (pmax 🝖 [≤]-predecessor gt)))
... | [∨]-introₗ le =
  _ ⇔-[ [↔]-intro (congruence₁(Option.map(_+ min))) (injective(Option.map(_+ min)) ⦃ map-injectivity ⦃ [↔]-to-[→] cancellationᵣ-injective [+]-cancellationᵣ ⦄ ⦄) ]
  _ ⇔-[ findUpperboundedMin-None-correctness{max −₀ min}{f ∘ (_+ min)} ]
  _ ⇔-[ [↔]-intro
    (\p{i} ord → p{i + min} ([∧]-intro ([≤]-of-[+]ᵣ {i}) (subtransitivityᵣ(_<_)(_≡_) ([<]-with-[+]ᵣ ord) ([↔]-to-[→] [−₀][+]-nullify2ᵣ le))))
    (\p{i} ([∧]-intro pmin pmax) → substitute₁ᵣ(IsFalse) (congruence₁(f) ([↔]-to-[→] [−₀][+]-nullify2ᵣ pmin)) (p{i −₀ min} ([<][−₀]ₗ-preserving pmin pmax)))
  ]
  _ ⇔-end

findBoundedMin-Some-correctness : (findBoundedMin min max f ≡ Some(n)) ↔ (IsTrue(f(n)) ∧ (min ≤ n < max) ∧ (∀{i} → (min ≤ i) → IsTrue(f(i)) → (n ≤ i)))
Tuple.left (findBoundedMin-Some-correctness {min}{max} {f} {n}) ([∧]-intro ([∧]-intro fnt ([∧]-intro pmin pmax)) minimal) with [≤]-or-[>] {min}{max}
... | [∨]-introᵣ gt
  rewrite [↔]-to-[→] [−₀]-when-0 ([≤]-predecessor gt)
  with () ← [≤]-to-[≯] pmin (subtransitivityᵣ(_≤_)(_<_) pmax gt)
... | [∨]-introₗ le
  with pminmax ← subtransitivityₗ(_<_)(_≤_) pmin pmax
  with eq ← ([↔]-to-[→] [−₀][+]-nullify2ᵣ pmin)
  = [∧]-intro ([∧]-intro (substitute₁ₗ(IsTrue) (congruence₁(f) eq) fnt) ([<][−₀]ₗ-preserving pmin pmax)) (\{i} → (\ord → subtransitivityᵣ(_≤_)(_≡_) ([≤][−₀]ₗ-preserving {b = min} ord) (inverseOperᵣ(_+_)(_−₀_) {y = min})) ∘ minimal{i + min} ([≤]-of-[+]ᵣ {i})) ⇒
    _ ⇒-[ [↔]-to-[←] (findUpperboundedMin-Some-correctness{max −₀ min}{f ∘ (_+ min)}{n −₀ min}) ]
    _ ⇒-[ (\prev → congruence₁(Option.map(_+ min)) prev 🝖 congruence₁(Some) eq) ]
    _ ⇒-end
Tuple.right (findBoundedMin-Some-correctness {min}{max} {f} {n}) p with [≤]-or-[>] {min}{max}
... | [∨]-introᵣ gt
  rewrite [↔]-to-[→] [−₀]-when-0 ([≤]-predecessor gt)
  with () ← p
... | [∨]-introₗ le
  = (let [∃]-intro m ⦃ [∧]-intro mmin q ⦄ = map-Some-value{f = _+ min}{o = findUpperboundedMin(max −₀ min) (f ∘ (_+ min))} p in
    findUpperboundedMin (max −₀ min) (f ∘ (_+ min)) 🝖[ _≡_ ]-[ q ]
    Some(m)                                           🝖[ _≡_ ]-[ congruence₁(Some) (inverseOperᵣ(_+_)(_−₀_) {m}{min}) ]-sym
    Some((m + min) −₀ min)                          🝖[ _≡_ ]-[ congruence₁(Some) (congruence₂-₁(_−₀_)(min) mmin) ]
    Some(n −₀ min)                                   🝖-end
  ) ⇒
  _ ⇒-[ [↔]-to-[→] (findUpperboundedMin-Some-correctness{max −₀ min}{f ∘ (_+ min)}{n −₀ min}) ]
  _ ⇒-[ (\([∧]-intro ([∧]-intro ft pmax) minimal) → [∧]-intro ([∧]-intro (substitute₁ᵣ(IsTrue) (congruence₁(f) ([↔]-to-[→] [−₀][+]-nullify2ᵣ pmin)) ft) ([∧]-intro pmin ([<][−₀]ₗ-preserving-converse pmin le pmax))) (\{i} pmini fi → [≤][−₀]ₗ-preserving-converse pmin pmini (minimal{i −₀ min} (substitute₁ₗ(IsTrue) (congruence₁(f) ([↔]-to-[→] [−₀][+]-nullify2ᵣ pmini)) fi)))) ]
  _ ⇒-end
  where
    map-ord : ∀{a b}{o} → (Option.map(_+ a) o ≡ Some b) → (a ≤ b) -- TODO: Is this neccessary? Maybe just use map-Some-value instead?
    map-ord {a} {.(x + a)} {Some x} [≡]-intro = [≤]-of-[+]ᵣ {x}

    pmin : min ≤ n
    pmin = map-ord{o = findUpperboundedMin (max −₀ min) (λ x → f (x + min))} p

findUpperboundedMax-findUpperboundedMin-equality : findUpperboundedMax max f ≡ Option.map ((max −₀_) ∘ 𝐒) (findUpperboundedMin max (f ∘ (max −₀_) ∘ 𝐒))
findUpperboundedMax-findUpperboundedMin-equality {𝟎}      {f} = [≡]-intro
findUpperboundedMax-findUpperboundedMin-equality {𝐒(max)} {f} with f(max) | inspect f(max)
... | 𝑇 | intro fmax = [≡]-intro
... | 𝐹 | intro fmax =
  _ 🝖[ _≡_ ]-[ findUpperboundedMax-findUpperboundedMin-equality {max} {f} ]
  Option.map ((max −₀_) ∘ 𝐒) (findUpperboundedMin max (f ∘ (max −₀_) ∘ 𝐒))          🝖[ _≡_ ]-[ (map-preserves-[∘] {f = max −₀_}{g = 𝐒}) {findUpperboundedMin max (f ∘ (max −₀_) ∘ 𝐒)} ]
  Option.map (max −₀_) (Option.map 𝐒 (findUpperboundedMin max (f ∘ (max −₀_) ∘ 𝐒))) 🝖-end

{-
open import Data
findUpperboundedMax-None-correctness : (findUpperboundedMax max f ≡ None) ↔ (∀{i} → (i < max) → IsFalse(f(i)))
findUpperboundedMax-None-correctness {max} {f} =
  findUpperboundedMax max f ≡ None                                                ⇔-[ [↔]-intro
    (findUpperboundedMax-findUpperboundedMin-equality{max}{f} 🝖_)
    (symmetry(_≡_) (findUpperboundedMax-findUpperboundedMin-equality{max}{f}) 🝖_)
  ]
  Option.map ((max −₀_) ∘ 𝐒) (findUpperboundedMin max (f ∘ (max −₀_) ∘ 𝐒)) ≡ None ⇔-[ [↔]-intro (congruence₁(Option.map((max −₀_) ∘ 𝐒))) (injective(Option.map((max −₀_) ∘ 𝐒)) ⦃ map-injectivity ⦃ {!TODO: Not actually injective. Only when less than max, and findUpperboundedMin is!} ⦄ ⦄) ]
  findUpperboundedMin max (f ∘ (max −₀_) ∘ 𝐒) ≡ None                              ⇔-[ findUpperboundedMin-None-correctness {max} {f ∘ (max −₀_) ∘ 𝐒} ]
  (∀{i} → (i < max) → IsFalse((f ∘ (max −₀_) ∘ 𝐒)(i)))                            ⇔-[ [↔]-intro
    (\p {i} ord → p{max −₀ 𝐒(i)} ([−₀]-strictly-lesser ord))
    (\p {i} ord → substitute₁ᵣ(IsFalse) (congruence₁(f) ([−₀]-with-[𝐒]ᵣ {max}{max −₀ 𝐒(i)} 🝖 congruence₁(𝐏) ([↔]-to-[→] [−₀]-nested-sameₗ ord))) (p{max −₀ 𝐒(i)} ([−₀]-strictly-lesser ord)))
  ]
  (∀{i} → (i < max) → IsFalse(f(i)))                                              ⇔-end
-}

{-
findBoundedMin : ℕ → ℕ → (ℕ → Bool) → Option(ℕ)
findBoundedMin a b f = Option.map toℕ (𝕟.findMin{b −₀ a}(f ∘ (_+ a) ∘ toℕ))

findBoundedMin-None-correctness : (a < b) → (findBoundedMin a b f ≡ None) ↔ (∀{i} → (a ≤ i) → (i < b) → IsFalse(f(i)))
findBoundedMin-None-correctness{a}{b}{f} ab
  with [↔]-intro l r ← 𝕟.findMin-None-correctness{b −₀ a}{f ∘ (_+ a) ∘ toℕ}
  = [↔]-intro (\p → congruence₁(Option.map toℕ) (l (\{i} → p ([≤]-of-[+]ᵣ {toℕ i}) {![<]-with-[+]-weak ([∨]-introₗ ([∧]-intro ? ?))!}))) (\p{i} ai ib → {!r ? {?}!})
-}

open import Data.List
import      Data.List.Functions as List
open import Data.List.Relation.Membership using (_∈_)
open import Data.List.Relation.Membership.Proofs
open import Data.List.Relation.Quantification
open import Data.List.Relation.Quantification.Universal.Functions
open import Data.List.Sorting
open import Numeral.Finite
import      Numeral.Finite.LinearSearch as 𝕟
import      Numeral.Finite.LinearSearch.Proofs.FindAll as 𝕟

findBoundedAll-correctness : AllElements(IsTrue ∘ f)(findBoundedAll a b f)
findBoundedAll-correctness {f} {a} {b} with 𝕟.findAll{b −₀ a} (f ∘ (_+ a) ∘ toℕ) | 𝕟.findAll-correctness{b −₀ a}{f ∘ (_+ a) ∘ toℕ}
... | ∅     | ∅      = ∅
... | _ ⊰ _ | p ⊰ ps = p ⊰ AllElements-mapᵣ ((_+ a) ∘ toℕ) id ps

postulate findBoundedAll-completeness : IsTrue(f(i)) → (a ≤ i) → (i < b) → (i ∈ findBoundedAll a b f)
-- findBoundedAll-completeness {f}{i}{a}{b} ai ib fi = {![∈]-map {f = toℕ} (𝕟.findAll-completeness{b −₀ a}{f ∘ (_+ a) ∘ toℕ}{fromℕ (i −₀ a) ⦃ ? ⦄} ?)!}

postulate findBoundedAll-emptyness : (∀{i} → (a ≤ i) → (i < b) → IsFalse(f(i))) ↔ (findBoundedAll a b f ≡ ∅)


postulate findBoundedAll-sorted : Sorted(_≤?_)(findBoundedAll a b f)

postulate findBoundedAll-membership : (i ∈ findBoundedAll a b f) ↔ ((a ≤ i) ∧ (i < b) ∧ IsTrue(f(i)))

{-
findUpperboundedMin-findMin-equality : findUpperboundedMin max f ≡ Option.map (toℕ {max}) (𝕟.findMin(f ∘ toℕ))
findUpperboundedMin-findMin-equality {𝟎}     {f} = [≡]-intro
findUpperboundedMin-findMin-equality {𝐒 max} {f} with f(𝟎) | inspect f(𝟎)
... | 𝑇 | intro f0 = [≡]-intro
... | 𝐹 | intro f0 =
  Option.map 𝐒(findUpperboundedMin max (f ∘ 𝐒))                        🝖[ _≡_ ]-[ congruence₁(Option.map 𝐒) (findUpperboundedMin-findMin-equality {max} {f ∘ 𝐒}) ]
  Option.map(𝐒) (Option.map toℕ(𝕟.findMin(f ∘ 𝐒 ∘ toℕ {max})))   🝖[ _≡_ ]-[ {!!} ]
  Option.map(𝐒 ∘ toℕ) (𝕟.findMin(f ∘ 𝐒 ∘ toℕ {max}))             🝖[ _≡_ ]-[ {!!} ]
  Option.map(𝐒 ∘ toℕ) (𝕟.findMin(f ∘ toℕ {𝐒 max} ∘ 𝐒))           🝖[ _≡_ ]-[ {!!} ]
  Option.map(toℕ ∘ 𝐒) (𝕟.findMin(f ∘ toℕ {𝐒 max} ∘ 𝐒))           🝖[ _≡_ ]-[ {!!} ]
  Option.map(toℕ) (Option.map 𝐒(𝕟.findMin(f ∘ toℕ {𝐒 max} ∘ 𝐒))) 🝖-end
-}
