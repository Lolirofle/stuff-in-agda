module Numeral.Finite.LinearSearch.Proofs.FindMin where

import      Data.Option.Functions as Option
open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Logic
open import Data.Option
open import Data.Option.Equiv.Id
open import Data.Option.Quantifiers
open import Data.Option.Quantifiers.Proofs
open import Functional
open import Lang.Inspect
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Logic.Propositional.Theorems
open import Numeral.Finite
open import Numeral.Finite.LinearSearch
open import Numeral.Finite.Oper.Comparisons.Proofs
open import Numeral.Finite.Proofs
open import Numeral.Finite.Relation.Order as 𝕟 using (_≤_ ; _>_ ; _<_)
open import Numeral.Finite.Relation.Order.Proofs as 𝕟 using ([≤]-minimum ; [≤]-maximum)
open import Numeral.Natural
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Relator
open import Syntax.Implication
open import Type
open import Type.Properties.Decidable.Proofs

private variable n : ℕ
private variable i j min max : 𝕟(n)
private variable f : 𝕟(n) → Bool

module _
  {ℓ}
  (P : (n : ℕ) → (𝕟(n) → Bool) → Option(𝕟(n)) → Type{ℓ})
  (pz  : ∀{f} → P 𝟎 f None)
  (pst : ∀{x}{f} → IsTrue(f(𝟎)) → P(𝐒(x)) f (Some 𝟎))
  (psf : ∀{x}{y : (𝕟(x) → Bool) → Option(𝕟(x))}{f} → IsFalse(f(𝟎)) → (∀{f} → P x f (y f)) → P(𝐒(x)) f (Option.map 𝐒(y(f ∘ 𝐒))))
  where

  findMin-intro : ∀{n}{f} → P n f (findMin f)
  findMin-intro {𝟎}   {f} = pz
  findMin-intro {𝐒 n} {f} with f(𝟎) | inspect f(𝟎)
  … | 𝑇 | intro p = pst([↔]-to-[←] IsTrue.is-𝑇 p)
  … | 𝐹 | intro p = psf([↔]-to-[←] IsFalse.is-𝐹 p) (\{f} → findMin-intro{n}{f})

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
findMin-Some-correctness {n}{f} = findMin-intro(\n f o → ∀{min} → (o ≡ Some(min)) → IsTrue(f(min)))
  (\())
  (\{_}{f} ft eq → substitute₁ᵣ(IsTrue) (congruence₁(f) (injective(Some) eq)) ft)
  (\{_}{y}{f} ff prev → \{
    {𝟎}     eq →
      [≡]-intro ⇒
      ∃ₒₚₜ(Some(𝟎)) (_≡ 𝟎)                ⇒-[ substitute₁ₗ(\o → ∃ₒₚₜ(o) (_≡ 𝟎)) eq ]
      ∃ₒₚₜ(Option.map 𝐒(y(f ∘ 𝐒))) (_≡ 𝟎) ⇒-[ [↔]-to-[→] ([∃ₒₚₜ]-of-map {f = 𝐒}{o = y(f ∘ 𝐒)}{P = _≡ 𝟎}) ]
      ∃ₒₚₜ(y(f ∘ 𝐒)) ((_≡ 𝟎) ∘ 𝐒)         ⇒-[ [∃ₒₚₜ]-map {P = (_≡ 𝟎) ∘ 𝐒}{Q = const ⊥}{o = y(f ∘ 𝐒)} (\()) ]
      ∃ₒₚₜ(y(f ∘ 𝐒)) (const ⊥)            ⇒-[ [∃ₒₚₜ]-of-⊥ {o = y(f ∘ 𝐒)} ]
      ⊥                                   ⇒-[ [⊥]-elim ]
      IsTrue(f(𝟎))                        ⇒-end ;
    {𝐒 min} eq → prev(injective(Option.map 𝐒) ⦃ map-injectivity ⦄ eq)
  })

findMin-minimal-true : (findMin f ≡ Some(min)) → IsTrue(f(i)) → (min ≤ i)
findMin-minimal-true {𝐒 n} {f} {min}   {i}   eq        p with f(𝟎) | inspect f(𝟎)
findMin-minimal-true {𝐒 n} {f} {.𝟎}    {i}   [≡]-intro p | 𝑇 | intro f0 = 𝕟.[≤]-minimum {n = 𝐒 n}{a = i}
findMin-minimal-true {𝐒 n} {f} {𝟎}     {i}   eq        p | 𝐹 | intro f0 with findMin{n} (f ∘ 𝐒)
findMin-minimal-true {𝐒 n} {f} {𝟎}     {i}   ()        p | 𝐹 | intro f0 | None
findMin-minimal-true {𝐒 n} {f} {𝟎}     {i}   ()        p | 𝐹 | intro f0 | Some _
findMin-minimal-true {𝐒 n} {f} {𝐒 min} {𝟎}   eq        p | 𝐹 | intro f0 = disjointness p ([↔]-to-[←] IsFalse.is-𝐹 f0)
findMin-minimal-true {𝐒 n} {f} {𝐒 min} {𝐒 i} eq        p | 𝐹 | intro f0 = findMin-minimal-true {n} {f ∘ 𝐒} {min} {i} (injective(Option.map 𝐒) ⦃ map-injectivity ⦄ eq) p

findMin-minimal-false : (findMin f ≡ Some(min)) → (min > i) → IsFalse(f(i))
findMin-minimal-false {n}{f}{min}{i} eq =
  (min > i)      ⇒-[ [↔]-to-[←] decider-true ∘ substitute₁ₗ(IsTrue) (⋚-elim₃-negation-distribution {x = min}{y = i}) ]
  ¬ (min ≤ i)    ⇒-[ contrapositiveᵣ(findMin-minimal-true{n}{f}{min}{i} eq) ]
  ¬ IsTrue(f(i)) ⇒-[ [↔]-to-[←] false-true-opposites ]
  IsFalse(f(i))  ⇒-end
