module Numeral.FiniteStrict.Bound{ℓ} where

import Lvl
open import Syntax.Number
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.FiniteStrict
open import Numeral.Natural hiding (𝐏)
open import Numeral.Natural.Function
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Relation{ℓ}
open import Relator.Equals{ℓ}{0}
open import Relator.Equals.Theorems{ℓ}{0}

bound-𝐒 : ∀{n} → 𝕟(n) → 𝕟(ℕ.𝐒(n))
bound-𝐒 (𝟎)    = 𝟎
bound-𝐒 (𝐒(n)) = 𝐒(bound-𝐒 (n))

bound-[+] : ∀{n₁ n₂} → 𝕟(n₁) → 𝕟(n₁ + n₂)
bound-[+] (𝟎) = 𝟎
bound-[+] {ℕ.𝐒(n₁)}{n₂}(𝐒(n)) = 𝐒(bound-[+] {n₁}{n₂} (n))

bound-maxₗ : ∀{n₁ n₂} → 𝕟(n₁) → 𝕟(max n₁ n₂)
bound-maxₗ {n₁}{n₂} (n) = [≡]-substitutionₗ (Theorems.max-elementary{ℓ}{n₁}{n₂}) {𝕟} (bound-[+] {n₁}{n₂ −₀ n₁} (n))

bound-maxᵣ : ∀{n₁ n₂} → 𝕟(n₂) → 𝕟(max n₁ n₂)
bound-maxᵣ {n₁}{n₂} (n) = [≡]-substitutionᵣ (Theorems.max-commutativity{ℓ}{n₂}{n₁}) {𝕟} (bound-maxₗ {n₂}{n₁} (n))

{-instance
  postulate downscale-instance : ∀{n} → ⦃ nfin : 𝕟(ℕ.𝐒(n)) ⦄ → ⦃ _ : [𝕟]-to-[ℕ]{ℕ.𝐒(n)}(nfin) lteq2 n ⦄ → 𝕟(n)
-}
