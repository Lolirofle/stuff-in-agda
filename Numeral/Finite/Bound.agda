module Numeral.Finite.Bound where

import Lvl
open import Syntax.Number
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Finite
open import Numeral.Natural hiding (𝐏)
open import Numeral.Natural.Function
open import Numeral.Natural.Function.Proofs
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Operator.Properties

bound-[≤] : ∀{a b} → ⦃ _ : (a ≤ b) ⦄ → 𝕟(a) → 𝕟(b)
bound-[≤] {𝟎}   {_}   ⦃ p ⦄            ()
bound-[≤] {𝐒 a} {𝐒 b} ⦃ p ⦄            𝟎     = 𝟎
bound-[≤] {𝐒 a} {𝐒 b} ⦃ [≤]-with-[𝐒] ⦄ (𝐒 n) = 𝐒(bound-[≤] n)

bound-𝐒 : ∀{n} → 𝕟(n) → 𝕟(ℕ.𝐒(n))
bound-𝐒 (𝟎)    = 𝟎
bound-𝐒 (𝐒(n)) = 𝐒(bound-𝐒(n))

{-
bound-𝐏 : ∀{n} → (a : 𝕟(ℕ.𝐒(n))) → ⦃ _ : a <? maximum ⦄ → 𝕟(n)
bound-𝐏 (𝟎)    = ?
bound-𝐏 (𝐒(n)) = ?
-}

bound-[+] : ∀{n₁ n₂} → 𝕟(n₁) → 𝕟(n₁ + n₂)
bound-[+] (𝟎) = 𝟎
bound-[+] {ℕ.𝐒(n₁)}{n₂}(𝐒(n)) = 𝐒(bound-[+] {n₁}{n₂} (n))

bound-maxₗ : ∀{n₁ n₂} → 𝕟(n₁) → 𝕟(max n₁ n₂)
bound-maxₗ {n₁}{n₂} (n) = bound-[≤] n -- [≡]-substitutionₗ (max-elementary{n₁}{n₂}) {𝕟} (bound-[+] {n₁}{n₂ −₀ n₁} (n))

bound-maxᵣ : ∀{n₁ n₂} → 𝕟(n₂) → 𝕟(max n₁ n₂)
bound-maxᵣ {n₁}{n₂} (n) = bound-[≤] n -- [≡]-substitutionᵣ (commutativity(max) {n₂}{n₁}) {𝕟} (bound-maxₗ {n₂}{n₁} (n))

bound-minₗ : ∀{n₁ n₂} → 𝕟(min n₁ n₂) → 𝕟(n₁)
bound-minₗ {n₁}{n₂} (n) = bound-[≤] n

bound-minᵣ : ∀{n₁ n₂} → 𝕟(min n₁ n₂) → 𝕟(n₂)
bound-minᵣ {n₁}{n₂} (n) = bound-[≤] n

{-instance
  postulate downscale-instance : ∀{n} → ⦃ nfin : 𝕟(ℕ.𝐒(n)) ⦄ → ⦃ _ : [𝕟]-to-[ℕ]{ℕ.𝐒(n)}(nfin) lteq2 n ⦄ → 𝕟(n)
-}

-- TODO: bound-shrink : ∀{n} → (i : 𝕟(n)) → 𝕟(ℕ.𝐒([𝕟]-to-[ℕ](i)))

-- TODO: bound-𝐏 : ∀{n} → 𝕟(n) → 𝕟(ℕ.𝐏(n)). How to prove stuff inside if-statements? if(P) then (in here, how to prove that (P ≡ 𝑇)?)
-- or maybe instead: bound-𝐏 : ∀{n} → (nfin : 𝕟(𝐒(n))) → ⦃ _ : [𝕟]-to-[ℕ](nfin) < n ⦄ → 𝕟(n)
