module Numeral.Finite.Proofs where

import Lvl
open import Data.Boolean.Stmt
open import Syntax.Number
open import Logic.Computability.Binary
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Finite
open import Numeral.Natural hiding (𝐏)
open import Numeral.Natural.Function
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Computability
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function.Domain

bounded : ∀{n : ℕ}{x : 𝕟(𝐒(n))} → (𝕟-to-ℕ(x) < 𝐒(n))
bounded{_}   {𝟎}    = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄
bounded{𝐒(n)}{𝐒(x)} = [≤]-with-[𝐒] ⦃ bounded{n}{x} ⦄

-- TODO: inverse1 : ∀{n}{x} → (x ≤ n) → ([𝕟]-to-[ℕ] ∘ [ℕ]-to-[𝕟])(x) ≡ x
-- TODO: inverse2 : ∀{n x} → ([ℕ]-to-[𝕟] ∘ [𝕟]-to-[ℕ])(x) ≡ x

instance
  [<]-of-𝕟-to-ℕ : ∀{N : ℕ}{n : 𝕟(N)} → (𝕟-to-ℕ (n) < N)
  [<]-of-𝕟-to-ℕ {𝟎} {()}
  [<]-of-𝕟-to-ℕ {𝐒 N} {𝟎}   = [≤]-with-[𝐒]
  [<]-of-𝕟-to-ℕ {𝐒 N} {𝐒 n} = [≤]-with-[𝐒] ⦃ [<]-of-𝕟-to-ℕ {N} {n} ⦄

{- TODO: Is this not working because of proof relevancy?
𝕟-conversion-inverse : ∀{N : ℕ}{n : 𝕟(N)} → (ℕ-to-𝕟 (𝕟-to-ℕ (n)) ⦃ [↔]-to-[→] (ComputablyDecidable.proof-istrue(_<_) {y = N}) ([<]-of-𝕟-to-ℕ {n = n}) ⦄ ≡ n)
𝕟-conversion-inverse {𝟎}   {()}
𝕟-conversion-inverse {𝐒 N} {𝟎}   = [≡]-intro
𝕟-conversion-inverse {𝐒 N} {𝐒 n} = [≡]-with(𝐒) {!(𝕟-conversion-inverse {N} {n})!} 
-}

ℕ-conversion-inverse : ∀{N n : ℕ} → ⦃ _ : IsTrue(n <? N) ⦄ → (𝕟-to-ℕ (ℕ-to-𝕟 (n) {N}) ≡ n)
ℕ-conversion-inverse {𝐒 N} {𝟎}   = [≡]-intro
ℕ-conversion-inverse {𝐒 N} {𝐒 n} = [≡]-with(𝐒) (ℕ-conversion-inverse {N} {n})
