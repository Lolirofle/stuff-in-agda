module Numeral.Natural.LinearSearchDecidable where -- TODO: Maybe move and rename to Numeral.Natural.Sequence.BoundedSearch

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

findUpperBoundedMaxIndex : (f : ℕ → Bool) → ℕ → Option(ℕ)
findUpperBoundedMaxIndex f(i) with f(i)
findUpperBoundedMaxIndex f(i)    | 𝑇 = Some i
findUpperBoundedMaxIndex f(𝟎)    | 𝐹 = None
findUpperBoundedMaxIndex f(𝐒(i)) | 𝐹 = findUpperBoundedMaxIndex f(i)

findMaxIndexInRange : (ℕ → Bool) → ℕ → ℕ → Option(ℕ)
findMaxIndexInRange f min max = Option.map (_+ min) (findUpperBoundedMaxIndex (f ∘ (_+ min)) (max −₀ min))

open import Data
open import Lang.Inspect
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator.Properties
open import Structure.Relator

findUpperBoundedMaxIndex-correctness : ∀{f}{max i} → (findUpperBoundedMaxIndex f(max) ≡ Some(i)) → ((i ≤ max) ∧ IsTrue(f(i)))
findUpperBoundedMaxIndex-correctness {f} {max}    {i} p with f(max) | inspect f(max)
findUpperBoundedMaxIndex-correctness {f} {max}    {.max} [≡]-intro | 𝑇 | intro eq = [∧]-intro (reflexivity(_≤_)) (substitute₁ₗ(IsTrue) eq <>)
findUpperBoundedMaxIndex-correctness {f} {𝟎}      {i}    ()        | 𝐹 | _
findUpperBoundedMaxIndex-correctness {f} {𝐒(max)} {i}    p         | 𝐹 | intro eq with findUpperBoundedMaxIndex-correctness {f} {max} {i} p
... | [∧]-intro a b = [∧]-intro ([≤]-successor a) b

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
