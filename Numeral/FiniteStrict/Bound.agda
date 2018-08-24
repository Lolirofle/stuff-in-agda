module Numeral.FiniteStrict.Bound{ℓ} where

import Lvl
open import Syntax.Number
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.FiniteStrict
open import Numeral.Natural hiding (𝐏)
open import Numeral.Natural.Function
open import Numeral.Natural.Function.Proofs{ℓ}
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Relation{ℓ}
open import Relator.Equals{ℓ}{0}
open import Relator.Equals.Proofs{ℓ}{0}

bound-𝐒 : ∀{n} → 𝕟(n) → 𝕟(ℕ.𝐒(n))
bound-𝐒 (𝟎)    = 𝟎
bound-𝐒 (𝐒(n)) = 𝐒(bound-𝐒 (n))

bound-[+] : ∀{n₁ n₂} → 𝕟(n₁) → 𝕟(n₁ + n₂)
bound-[+] (𝟎) = 𝟎
bound-[+] {ℕ.𝐒(n₁)}{n₂}(𝐒(n)) = 𝐒(bound-[+] {n₁}{n₂} (n))

bound-maxₗ : ∀{n₁ n₂} → 𝕟(n₁) → 𝕟(max n₁ n₂)
bound-maxₗ {n₁}{n₂} (n) = [≡]-substitutionₗ (max-elementary{n₁}{n₂}) {𝕟} (bound-[+] {n₁}{n₂ −₀ n₁} (n))

bound-maxᵣ : ∀{n₁ n₂} → 𝕟(n₂) → 𝕟(max n₁ n₂)
bound-maxᵣ {n₁}{n₂} (n) = [≡]-substitutionᵣ (max-commutativity{n₂}{n₁}) {𝕟} (bound-maxₗ {n₂}{n₁} (n))

postulate bound-minₗ : ∀{n₁ n₂} → 𝕟(min n₁ n₂) → 𝕟(n₁)
-- bound-minₗ {n₁}{n₂} (n) = TODO: Use the proof that min always is one of its args

postulate bound-minᵣ : ∀{n₁ n₂} → 𝕟(min n₁ n₂) → 𝕟(n₂)
-- bound-minᵣ {n₁}{n₂} (n) = 

{-instance
  postulate downscale-instance : ∀{n} → ⦃ nfin : 𝕟(ℕ.𝐒(n)) ⦄ → ⦃ _ : [𝕟]-to-[ℕ]{ℕ.𝐒(n)}(nfin) lteq2 n ⦄ → 𝕟(n)
-}

-- TODO: bound-shrink : ∀{n} → (i : 𝕟(n)) → 𝕟(ℕ.𝐒([𝕟]-to-[ℕ](i)))

-- TODO: bound-𝐏 : ∀{n} → 𝕟(n) → 𝕟(ℕ.𝐏(n)). How to prove stuff inside if-statements? if(P) then (in here, how to prove that (P ≡ 𝑇)?)
-- or maybe instead: bound-𝐏 : ∀{n} → (nfin : 𝕟(𝐒(n))) → ⦃ _ : [𝕟]-to-[ℕ](nfin) < n ⦄ → 𝕟(n)
