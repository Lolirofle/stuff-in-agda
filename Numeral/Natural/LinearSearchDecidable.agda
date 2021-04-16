module Numeral.Natural.LinearSearchDecidable where -- TODO: Maybe move and rename to Numeral.Natural.Sequence.BoundedSearch
-- TODO: Maybe more natural to use 𝕟 (finite naturals) instead of ℕ (naturals)?

open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.List
import      Data.List.Functions as List
open import Data.List.Relation.Membership using (_∈_)
open import Data.List.Relation.Membership.Proofs
open import Data.List.Relation.Quantification
open import Data.List.Relation.Quantification.Proofs
open import Data.List.Sorting
open import Data.Option
import      Data.Option.Functions as Option
open import Functional
open import Logic.Propositional
open import Numeral.Finite
import      Numeral.Finite.LinearSearch as 𝕟
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation.Order
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function

private variable a b n i j : ℕ
private variable f : ℕ → Bool

{-
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Option
import      Data.Option.Functions as Option
open import Functional
open import Logic
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Relation.Order
open import Structure.Relator.Ordering

-- Finds the maximal argument satisfying the given argument within the given search upper bound by searching linearly.
-- Examples:
--   findUpperBoundedMax(10 ∣?_) 5   = None
--   findUpperBoundedMax(10 ∣?_) 20  = Some 20
--   findUpperBoundedMax(10 ∣?_) 22  = Some 20
--   findUpperBoundedMax(10 ∣?_) 100 = Some 100
--   findUpperBoundedMax(10 ∣?_) 102 = Some 100
findUpperBoundedMax : (ℕ → Bool) → ℕ → Option(ℕ)
findUpperBoundedMax f(i) with f(i)
findUpperBoundedMax f(i)    | 𝑇 = Some i
findUpperBoundedMax f(𝟎)    | 𝐹 = None
findUpperBoundedMax f(𝐒(i)) | 𝐹 = findUpperBoundedMax f(i)

findMaxIndexInRange : (ℕ → Bool) → ℕ → ℕ → Option(ℕ)
findMaxIndexInRange f min max = Option.map (_+ min) (findUpperBoundedMax (f ∘ (_+ min)) (max −₀ min))

-- Finds the minimal argument satisfying the given argument within the given search upper bound by searching linearly.
-- Examples:
--   findUpperBoundedMin(10 ∣?_) 5   = None
--   findUpperBoundedMin(10 ∣?_) 20  = Some 10
--   findUpperBoundedMin(10 ∣?_) 22  = Some 10
--   findUpperBoundedMin(10 ∣?_) 100 = Some 10
--   findUpperBoundedMax(10 ∣?_) 102 = Some 10
findUpperBoundedMin : (ℕ → Bool) → ℕ → Option(ℕ)
findUpperBoundedMin f(i) with f(𝟎)
findUpperBoundedMin f(i)    | 𝑇 = Some 𝟎
findUpperBoundedMin f(𝟎)    | 𝐹 = None
findUpperBoundedMin f(𝐒(i)) | 𝐹 = Option.map 𝐒 (findUpperBoundedMin (f ∘ 𝐒)(i))

open import Data
open import Data.Boolean.Stmt.Proofs
open import Data.Option.Equiv.Id
open import Lang.Inspect
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Structure.Relator

findUpperBoundedMax-correctness : ∀{f}{max i} → (findUpperBoundedMax f(max) ≡ Some(i)) → ((i ≤ max) ∧ IsTrue(f(i)))
findUpperBoundedMax-correctness {f} {max}    {i} p with f(max) | inspect f(max)
findUpperBoundedMax-correctness {f} {max}    {.max} [≡]-intro | 𝑇 | intro eq = [∧]-intro (reflexivity(_≤_)) (substitute₁ₗ(IsTrue) eq <>)
findUpperBoundedMax-correctness {f} {𝟎}      {i}    ()        | 𝐹 | _
findUpperBoundedMax-correctness {f} {𝐒(max)} {i}    p         | 𝐹 | intro eq with findUpperBoundedMax-correctness {f} {max} {i} p
... | [∧]-intro a b = [∧]-intro ([≤]-successor a) b

findUpperBoundedMin-correctness : ∀{f}{max i} → (findUpperBoundedMin f(max) ≡ Some(i)) → ((i ≤ max) ∧ IsTrue(f(i)))
findUpperBoundedMin-correctness {f} {max}   {i}   p with f(𝟎) | inspect f(𝟎)
findUpperBoundedMin-correctness {f} {max}   {.𝟎}  [≡]-intro | 𝑇 | intro eq = [∧]-intro [≤]-minimum ([↔]-to-[←] IsTrue.is-𝑇 eq)
findUpperBoundedMin-correctness {f} {𝐒 max} {𝟎}   p         | 𝐹 | intro eq with findUpperBoundedMin (f ∘ 𝐒) max
findUpperBoundedMin-correctness {f} {𝐒 max} {𝟎}   ()        | 𝐹 | intro eq | None
findUpperBoundedMin-correctness {f} {𝐒 max} {𝟎}   ()        | 𝐹 | intro eq | Some _
findUpperBoundedMin-correctness {f} {𝐒 max} {𝐒 i} p         | 𝐹 | intro eq = [∧]-map (\p → [≤]-with-[𝐒] ⦃ p ⦄) id (findUpperBoundedMin-correctness {f ∘ 𝐒} {max} {i} (injective(Option.map 𝐒) ⦃ map-injectivity ⦄ p))

findUpperBoundedMin-minimal : ∀{f}{max i j} → (findUpperBoundedMin f(max) ≡ Some(i)) → IsTrue(f(j)) → (i ≤ j)
findUpperBoundedMin-minimal {i = 𝟎} {_} p q = [≤]-minimum
findUpperBoundedMin-minimal {i = 𝐒 i} {𝟎} p q = {!!}
findUpperBoundedMin-minimal {i = 𝐒 i} {𝐒 j} p q = [≤]-with-[𝐒] ⦃ findUpperBoundedMin-minimal {i = i}{j} {!!} q ⦄

-- foldRange : ()

{-
searchUntilUpperBound : (f : ℕ → Bool) → ∃(IsTrue ∘ f) → ℕ
searchUntilUpperBound f ([∃]-intro upperBound ⦃ proof ⦄) = {!fold!}

searchUntilUpperBoundProof : ∀{f}{upperBound} → (IsTrue ∘ f)(searchUntilUpperBound f upperBound)
searchUntilUpperBoundProof = {!!}

bruteforceMinExistence : ∀{ℓ} → (P : ℕ → Stmt{ℓ}) → ⦃ ComputablyDecidable(P) ⦄ → ∃(P) → ∃(Weak.Properties.MinimumOf(_≤_)(P))
∃.witness (bruteforceMinExistence P upperBound) = {!!}
∃.proof   (bruteforceMinExistence P upperBound) = {!!}
-}
-}
