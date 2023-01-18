module Numeral.Finite.LinearSearch.Proofs.FindAll where

import      Data.List.Functions as List
import      Data.Option.Functions as Option
open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Logic
open import Data.List
open import Data.List.Proofs
open import Data.List.Relation.Membership using (_∈_)
open import Data.List.Relation.Membership.Proofs
open import Data.List.Relation.Pairwise
open import Data.List.Relation.Pairwise.Proofs
open import Data.List.Relation.Quantification
open import Data.List.Relation.Quantification.Universal.Functions
open import Data.List.Sorting
open import Functional
open import Lang.Inspect
open import Logic.Propositional
open import Numeral.Finite
open import Numeral.Finite.LinearSearch
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Natural
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Syntax.Transitivity
open import Type

private variable n : ℕ
private variable i j : 𝕟(n)
private variable f : 𝕟(n) → Bool

module _
  {ℓ}
  (P : (n : ℕ) → (𝕟(n) → Bool) → List(𝕟(n)) → Type{ℓ})
  (pz  : ∀{f} → P 𝟎 f ∅)
  (pst : ∀{x}{y}{f} → IsTrue(f(𝟎))  → P x (f ∘ 𝐒) y → P(𝐒(x)) f (𝟎 ⊰ List.map 𝐒(y)))
  (psf : ∀{x}{y}{f} → IsFalse(f(𝟎)) → P x (f ∘ 𝐒) y → P(𝐒(x)) f (List.map 𝐒(y)))
  where

  findAll-intro : ∀{n}{f} → P n f (findAll f)
  findAll-intro {𝟎}   {f} = pz
  findAll-intro {𝐒 n} {f} with f(𝟎) | inspect f(𝟎)
  … | 𝑇 | intro p = pst([↔]-to-[←] IsTrue.is-𝑇 p) (findAll-intro{n}{f ∘ 𝐒})
  … | 𝐹 | intro p = psf([↔]-to-[←] IsFalse.is-𝐹 p) (findAll-intro{n}{f ∘ 𝐒})

findAll-correctness : AllElements(IsTrue ∘ f)(findAll f)
findAll-correctness {𝟎}   {f} = ∅
findAll-correctness {𝐒 n} {f} with f(𝟎) | inspect f(𝟎)
... | 𝑇 | intro f0 = ([↔]-to-[←] IsTrue.is-𝑇 f0) ⊰ (AllElements-mapᵣ 𝐒 id (findAll-correctness {n}{f ∘ 𝐒}))
... | 𝐹 | intro _  = AllElements-mapᵣ 𝐒 id (findAll-correctness {n}{f ∘ 𝐒})

findAll-completeness : IsTrue(f(i)) → (i ∈ findAll f)
findAll-completeness {𝐒 n} {f} {i}   p with f(𝟎) | inspect f(𝟎)
findAll-completeness {𝐒 n} {f} {𝟎}   p | 𝑇 | intro _  = • [≡]-intro
findAll-completeness {𝐒 n} {f} {𝐒 i} p | 𝑇 | intro _  = ⊰ [∈]-mapᵣ (findAll-completeness{n}{f ∘ 𝐒}{i} p)
findAll-completeness {𝐒 n} {f} {𝟎}   p | 𝐹 | intro f0 with () ← disjointness p ([↔]-to-[←] IsFalse.is-𝐹 f0)
findAll-completeness {𝐒 n} {f} {𝐒 i} p | 𝐹 | intro _  = [∈]-mapᵣ (findAll-completeness {n} {f ∘ 𝐒} {i} p)

findAll-sorted : Sorted(_≤?_)(findAll f)
findAll-sorted {𝟎}      {f} = AdjacentlyPairwise.empty
findAll-sorted {𝐒 𝟎} {f} with f(𝟎) | inspect f(𝟎)
findAll-sorted {𝐒 𝟎} {f} | 𝑇 | intro f0 = AdjacentlyPairwise.single
findAll-sorted {𝐒 𝟎} {f} | 𝐹 | intro f0 = AdjacentlyPairwise.empty
findAll-sorted {𝐒(𝐒 n)} {f} with f(𝟎) | f(𝐒 𝟎) | AdjacentlyPairwise-map {f = id}{_▫₁_ = IsTrue ∘₂ _≤?_}{g = 𝐒}{_▫₂_ = IsTrue ∘₂ _≤?_} id (findAll-sorted {𝐒 n}{f ∘ 𝐒})
... | 𝑇 | 𝑇 | prev = AdjacentlyPairwise.step <> prev
... | 𝑇 | 𝐹 | prev = AdjacentlyPairwise-prepend-min (\{ {𝟎} → <> ; {𝐒 _} → <>}) prev
... | 𝐹 | 𝑇 | prev = prev
... | 𝐹 | 𝐹 | prev = prev

findAll-first-findMin : (List.first(findAll f) ≡ findMin f)
findAll-first-findMin {𝟎} {f} = [≡]-intro
findAll-first-findMin {𝐒 n} {f} with f(𝟎)
... | 𝑇 = [≡]-intro
... | 𝐹 =
  List.first((if 𝐹 then (_⊰_ 𝟎) else id) (List.map 𝐒(findAll(f ∘ 𝐒)))) 🝖[ _≡_ ]-[]
  List.first(List.map 𝐒(findAll(f ∘ 𝐒)))                               🝖[ _≡_ ]-[ first-preserve-map ]
  Option.map 𝐒(List.first(findAll(f ∘ 𝐒)))                             🝖[ _≡_ ]-[ congruence₁(Option.map 𝐒) (findAll-first-findMin {n}{f ∘ 𝐒}) ]
  Option.map 𝐒(findMin(f ∘ 𝐒))                                         🝖-end
