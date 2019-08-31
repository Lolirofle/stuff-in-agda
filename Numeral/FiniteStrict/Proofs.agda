module Numeral.FiniteStrict.Proofs{ℓ} where

import Lvl
open import Syntax.Number
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.FiniteStrict
open import Numeral.Natural hiding (𝐏)
open import Numeral.Natural.Function
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs{ℓ}
open import Numeral.Natural.Relation.Order{ℓ}
open import Numeral.Natural.Relation.Order.Proofs{ℓ}
open import Relator.Equals{ℓ}{0}
open import Relator.Equals.Proofs{ℓ}{0}

bounded : ∀{n : ℕ}{x : 𝕟(𝐒(n))} → ([𝕟]-to-[ℕ](x) < 𝐒(n))
bounded{_}   {𝟎}    = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄
bounded{𝐒(n)}{𝐒(x)} = [≤]-with-[𝐒] ⦃ bounded{n}{x} ⦄

-- TODO: inverse1 : ∀{n}{x} → (x ≤ n) → ([𝕟]-to-[ℕ] ∘ [ℕ]-to-[𝕟])(x) ≡ x
-- TODO: inverse2 : ∀{n x} → ([ℕ]-to-[𝕟] ∘ [𝕟]-to-[ℕ])(x) ≡ x
