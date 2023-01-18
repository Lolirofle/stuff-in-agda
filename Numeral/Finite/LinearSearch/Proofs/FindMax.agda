module Numeral.Finite.LinearSearch.Proofs.FindMax where

import      Data.Option.Functions as Option
open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Logic
open import Data.Option
open import Data.Option.Equiv.Id
open import Functional
open import Lang.Inspect
open import Logic.Propositional
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Finite.LinearSearch
open import Numeral.Natural
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Type

private variable n : ℕ
private variable i j min max : 𝕟(n)
private variable f : 𝕟(n) → Bool

module _
  {ℓ}
  (P : (n : ℕ) → (𝕟(n) → Bool) → Option(𝕟(n)) → Type{ℓ})
  (pz  : ∀{f} → P 𝟎 f None)
  (pst : ∀{x}{f} → IsTrue(f(maximum)) → P(𝐒(x)) f (Some maximum))
  (psf : ∀{x}{y : (𝕟(x) → Bool) → Option(𝕟(x))}{f} → IsFalse(f(maximum)) → (∀{f} → P x f (y f)) → P(𝐒(x)) f (Option.map bound-𝐒(y (f ∘ bound-𝐒))))
  where

  findMax-intro : ∀{n}{f} → P n f (findMax f)
  findMax-intro {𝟎}   {f} = pz
  findMax-intro {𝐒 n} {f} with f(maximum) | inspect f(maximum)
  … | 𝑇 | intro p = pst([↔]-to-[←] IsTrue.is-𝑇 p)
  … | 𝐹 | intro p = psf([↔]-to-[←] IsFalse.is-𝐹 p) (\{f} → findMax-intro{n}{f})

findMax-None-correctness : (findMax f ≡ None) ↔ (∀{i} → IsFalse(f(i)))
findMax-None-correctness = [↔]-intro l r where
  l : (findMax f ≡ None) ← (∀{i} → IsFalse(f(i)))
  l {n}{f} = findMax-intro(\n f o → (o ≡ None) ← (∀{i} → IsFalse(f(i))))
    (\_ → [≡]-intro)
    (\p fmax → [⊥]-elim (disjointness p fmax))
    (\p prev fmax → congruence₁(Option.map bound-𝐒) (prev fmax))

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

{-
import      Numeral.Finite.Oper as 𝕟
import      Numeral.Natural.Relation as ℕ

findMin-findMax : Option.map 𝕟.Wrapping.flip (findMin(f ∘ 𝕟.Wrapping.flip)) ≡ findMax f
findMin-findMax = findMax-intro(\n f o → Option.map 𝕟.Wrapping.flip (findMin(f ∘ 𝕟.Wrapping.flip)) ≡ o)
  [≡]-intro
  (\{x}{f} → findMin-intro(\n f o → ⦃ pos : ℕ.Positive(n) ⦄ → IsTrue(f(minimum)) → Option.map(𝕟.Wrapping.flip) o ≡ Some maximum)
    (\ ⦃ ⦄)
    (\_ _ → [≡]-intro)
    (\pf _ pt → [⊥]-elim (disjointness pt pf))
    {𝐒 x}
    {f ∘ 𝕟.Wrapping.flip}
  )
  (\{x}{y}{f} pf prev → {!findMin-intro(\{ (𝐒 n) f o → ∀{y} → ⦃ pos : ℕ.Positive(𝐒 n) ⦄ → IsFalse(f(minimum)) → Option.map 𝕟.Wrapping.flip o ≡ Option.map bound-𝐒(y(f ∘ 𝕟.Wrapping.flip ∘ bound-𝐒))}) ? ? ? {𝐒 x}!} where
    test : 
  )
  {-
    findMin-intro(\{ 𝟎 _ _ → Unit ; (𝐒 n) f o → ∀{y} → ⦃ pos : ℕ.Positive(𝐒 n) ⦄ → IsFalse(f(minimum)) → Option.map 𝕟.Wrapping.flip o ≡ Option.map bound-𝐒(y(f ∘ bound-𝐒)) })
    {!!}
    {!!}
    {!!}
    {𝐒 x}
    {f ∘ 𝕟.Wrapping.flip}
    {y}
    pf
    -- (∀{f} → Option.map 𝕟.Wrapping.flip o ≡ y(f))
  -}
-}

{-
findMax-maximal-false : (findMax f ≡ Some(max)) → (i > max) → IsFalse(f(i))
findMax-maximal-false = findMax-intro(\n f o → ∀{max}{i} → (o ≡ Some(max)) → (i > max) → IsFalse(f(i)))
  {!!}
  {!!}
  (\{x}{y}{f} pf prev {max}{i} eq ord → {!!})
-}

{-
import Numeral.Finite.Relation.Order.Proofs as 𝕟

findMax-maximal-true : (findMax f ≡ Some(max)) → IsTrue(f(i)) → (i ≤ max)
findMax-maximal-true = findMax-intro(\n f o → ∀{max}{i} → (o ≡ Some(max)) → IsTrue(f(i)) → (i ≤ max))
  (\{_}{})
  (\{x} _ {max}{i} eq t → 𝕟.[≤][≡]-subtransitivityᵣ-raw {𝐒 x}{a = i}{𝐒 x}{b = maximum ⦃ _ ⦄}{c = max} ([≤]-maximum {a = i} (reflexivity(ℕ._≤_))) (sub₂(_≡_)(𝕟._≡_) (injective(Some) eq)))
  (\{
    {x}{y}{f} pf prev {max}  {𝟎}   ps pt → {!!} ;
    {x}{y}{f} pf prev {𝟎}    {𝐒 i} ps pt → {!!} ;
    {x}{y}{f} pf prev {𝐒 max}{𝐒 i} ps pt → prev{f ∘ 𝐒}{max}{i} {!!} pt
  })
-}

{-
findMax-maximal : (findMax f ≡ Some(max)) → IsTrue(f(i)) → (i ≤ max)
findMax-maximal {𝐒 n}{f} {max} {i} eq fi with f(maximum) | inspect f(maximum)
findMax-maximal {𝐒 n} {f} {.maximum} {i} [≡]-intro fi | 𝑇 | intro fmax = [≤]-maximum {𝐒 n}{i} (reflexivity(ℕ._≤_))
findMax-maximal {𝐒 n}{f} {max} {i} eq fi | 𝐹 | intro fmax with findMax(f ∘ bound-𝐒) | inspect findMax(f ∘ bound-𝐒)
... | Some x | intro p = {!findMax-maximal {n}{f ∘ bound-𝐒} {?} {?}!}
-}

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
--postulate findMax-maximal-true : (findMax f ≡ Some(max)) → IsTrue(f(i)) → (i ≤ max)
{-findMax-maximal {𝐒 n}{f} eq p with f(maximum) | inspect f(maximum)
findMax-maximal {𝐒 n} {f} {i = i} [≡]-intro p | 𝑇 | intro m = [≤]-maximum {𝐒 n}{i} (reflexivity(ℕ._≤_))
findMax-maximal {𝐒 n} {f} {i = i} eq p | 𝐹 | intro m with findMax{n} (f ∘ bound-𝐒) | inspect (findMax{n}) (f ∘ bound-𝐒)
findMax-maximal {𝐒 n} {f} {i = i} eq p | 𝐹 | intro m | Some x | intro findMax-x = {!findMax-maximal {n} {f ∘ bound-𝐒} {i = ?} !}
-}

{- TODO
test : ∀{i : 𝕟(𝐒(n))} → ¬(maximum{𝐒 n} < i)
test {𝟎}   {𝟎}   p = p
test {𝐒 n} {𝟎}   p = p
test {𝐒 n} {𝐒 i} p = test {n}{i} p

{-
findMax-maximal2 : (findMax f ≡ Some(max)) → (i > max) → IsFalse(f(i))
findMax-maximal2 {𝐒 n} {f} {max} {i} eq p with f(maximum) | inspect f(maximum)
findMax-maximal2 {𝐒 n} {f} {𝟎} {𝐒 i} eq p | 𝑇 | intro fmax with maximum-is-minimum-1(injective(Some) eq)
findMax-maximal2 {𝐒 .0} {f} {𝟎} {𝐒 ()} eq p | 𝑇 | intro fmax | [≡]-intro
findMax-maximal2 {𝐒 (𝐒 n)} {f} {𝐒 max} {𝐒 i} eq p | 𝑇 | intro fmax with f(bound-𝐒 maximum) | inspect (f ∘ bound-𝐒)(maximum)
findMax-maximal2 {𝐒 (𝐒 n)} {f} {𝐒 .maximum} {𝐒 i} [≡]-intro p | 𝑇 | intro fmax | 𝑇 | intro x with () ← test{n} p
findMax-maximal2 {𝐒 (𝐒 n)} {f} {𝐒 {.(𝐒 n)} .(maximum {𝐒 n})} {𝐒 {.(𝐒 n)} i} ([≡]-intro {x = .(Some (𝐒 {𝐒 n} (maximum {𝐒 n})))}) p | 𝑇 | intro fmax | 𝐹 | intro x with () ← test{n} p
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
