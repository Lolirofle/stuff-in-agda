module Numeral.Natural.Relation.Properties where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Induction
open import Numeral.Natural.Relation
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Type

[ℕ]-zero-or-nonzero : ∀{n : ℕ} → (n ≡ 𝟎)∨(n ≢ 𝟎)
[ℕ]-zero-or-nonzero {𝟎}    = [∨]-introₗ [≡]-intro
[ℕ]-zero-or-nonzero {𝐒(_)} = [∨]-introᵣ \()

[≡][ℕ]-excluded-middle : ∀{a b : ℕ} → (a ≡ b)∨(a ≢ b)
[≡][ℕ]-excluded-middle {𝟎}   {𝟎}    = [∨]-introₗ [≡]-intro
[≡][ℕ]-excluded-middle {𝟎}   {𝐒(_)} = [∨]-introᵣ \()
[≡][ℕ]-excluded-middle {𝐒(_)}{𝟎}    = [∨]-introᵣ \()
[≡][ℕ]-excluded-middle {𝐒(a)}{𝐒(b)} = [∨]-elim ([∨]-introₗ ∘ congruence₁(𝐒)) ([∨]-introᵣ ∘ (contrapositiveᵣ(injective(𝐒)))) ([≡][ℕ]-excluded-middle {a}{b})
