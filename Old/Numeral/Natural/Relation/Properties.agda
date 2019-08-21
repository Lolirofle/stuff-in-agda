module Numeral.Natural.Relation.Properties{ℓ} where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Propositional.Theorems{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Induction{ℓ}
open import Numeral.Natural.Relation{ℓ}
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Proofs{ℓ}{Lvl.𝟎}
open import Structure.Operator.Properties{ℓ}{Lvl.𝟎}
open import Structure.Relator.Ordering{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}
open import Type

[ℕ]-zero-or-nonzero : ∀{n : ℕ} → (n ≡ 𝟎)∨(n ≢ 𝟎)
[ℕ]-zero-or-nonzero {𝟎}    = [∨]-introₗ [≡]-intro
[ℕ]-zero-or-nonzero {𝐒(_)} = [∨]-introᵣ \()

[≡][ℕ]-excluded-middle : ∀{a b : ℕ} → (a ≡ b)∨(a ≢ b)
[≡][ℕ]-excluded-middle {𝟎}   {𝟎}    = [∨]-introₗ [≡]-intro
[≡][ℕ]-excluded-middle {𝟎}   {𝐒(_)} = [∨]-introᵣ \()
[≡][ℕ]-excluded-middle {𝐒(_)}{𝟎}    = [∨]-introᵣ \()
[≡][ℕ]-excluded-middle {𝐒(a)}{𝐒(b)} = [∨]-elim ([∨]-introₗ ∘ [≡]-with(𝐒)) ([∨]-introᵣ ∘ (contrapositiveᵣ [𝐒]-injectivity)) ([≡][ℕ]-excluded-middle {a}{b})
