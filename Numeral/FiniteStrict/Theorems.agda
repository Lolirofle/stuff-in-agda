module Numeral.FiniteStrict.Theorems{ℓ} where

import Lvl
open import Syntax.Number
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.FiniteStrict
open import Numeral.Natural hiding (𝐏)
open import Numeral.Natural.Function
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Relation.Order{ℓ}
open import Numeral.Natural.Relation.Order.Theorems{ℓ}
open import Relator.Equals{ℓ}{0}
open import Relator.Equals.Proofs{ℓ}{0}

postulate bounded : ∀{n : ℕ}{x : 𝕟(𝐒(n))} → ([𝕟]-to-[ℕ](x) < 𝐒(n))
