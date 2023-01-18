module Data.List.Functions.Proofs.Positional where

open import Data.List.Equiv
open import Data.List.Functions as List using (length ; insertIn) renaming (module LongOper to List)
open import Data.List
open import Functional
open import Logic.Propositional
import      Lvl
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Finite.Proofs
import      Numeral.Finite.Relation.Order as 𝕟
open import Numeral.Finite.Relation.Order.Proofs
open import Numeral.Finite
open import Numeral.Natural
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable T A B : Type{ℓ}
private variable N : ℕ
private variable n₁ n₂ : 𝕟(N)

module _ ⦃ equiv : Equiv{ℓₑ₁}(T) ⦄ ⦃ equiv-List : Equiv{ℓₑ₂}(List(T)) ⦄ ⦃ ext : Extensionality(equiv-List) ⦄ where
  private variable x y z x₁ x₂ : T
  private variable l l₁ l₂ l₃ l₄ : List(T)

  insertIn-function-raw : (x₁ ≡ x₂) → (l₁ ≡ l₂) → (n₁ 𝕟.≡ n₂) → (insertIn x₁ l₁ n₁ ≡ insertIn x₂ l₂ n₂)
  insertIn-function-raw                          {n₁ = 𝟎}   {n₂ = 𝟎}    ex el en = congruence₂(_⊰_) ex el
  insertIn-function-raw {l₁ = _ ⊰ _}{l₂ = _ ⊰ _} {n₁ = 𝐒 n₁}{n₂ = 𝐒 n₂} ex el en = congruence₂(_⊰_)
    ([∧]-elimₗ ([⊰]-generalized-cancellation el))
    (insertIn-function-raw{n₁ = n₁}{n₂ = n₂} ex ([∧]-elimᵣ ([⊰]-generalized-cancellation el)) en)

  insertIn-swapₗ : ∀{x y : T}{l}{n₁}{n₂}{n₃}{n₄} → (n₁ 𝕟.≤ n₃) → (n₁ 𝕟.≡ n₄) → (n₂ 𝕟.≡ 𝐒(n₃)) → (insertIn x (insertIn y l n₁) n₂ ≡ insertIn y (insertIn x l n₃) n₄)
  insertIn-swapₗ {l = l}     {𝟎}   {𝐒 𝟎}    {𝟎}   {𝟎}    n12 n14 n23 = reflexivity(_≡_)
  insertIn-swapₗ {l = l}     {𝟎}   {𝐒(𝐒 n₂)}{𝐒 n₃}{𝟎}    n12 n14 n23 = congruence₂-₂(_⊰_)(_) (insertIn-function-raw (reflexivity(_≡_)) (reflexivity(_≡_)) n23) -- (congruence₁(insertIn _ _) ([↔]-to-[←] [≡][≡?]-equivalence n23))
  insertIn-swapₗ {l = x ⊰ l} {𝐒 n₁}{𝐒(𝐒 n₂)}{𝐒 n₃}{𝐒 n₄} n12 n14 n23 = congruence₂-₂(_⊰_)(_) (insertIn-swapₗ {l = l} {n₁}{𝐒 n₂}{n₃}{n₄} n12 n14 n23)

  insertIn-swapᵣ : ∀{x y : T}{l}{n₁}{n₂}{n₃}{n₄} → (n₁ 𝕟.≥ n₃) → (𝐒(n₁) 𝕟.≡ n₄) → (n₂ 𝕟.≡ n₃) → (insertIn x (insertIn y l n₁) n₂ ≡ insertIn y (insertIn x l n₃) n₄)
  insertIn-swapᵣ{l = l}{n₁}{n₂}{n₃}{n₄} n13 n14 n23 = symmetry(_≡_) $ insertIn-swapₗ{l = l}
    (sub₂(𝕟._≥_)(Functional.swap(𝕟._≤_)) {n₁}{n₃} n13)
    ([≡]-symmetry-raw {a = n₂}{b = n₃} n23)
    ([≡]-symmetry-raw {a = 𝐒(n₁)}{b = n₄} n14)

  postulate insertIn-swapₗ' : ∀{x y : T}{l}{n₁}{n₂}{n₃}{n₄} → ((n₁ 𝕟.≤ n₃) ∨ (n₄ 𝕟.≤ n₃)) ∨ (((n₁ 𝕟.< n₂) ∨ (n₄ 𝕟.< n₂))) → (n₁ 𝕟.≡ n₄) → (n₂ 𝕟.≡ 𝐒(n₃)) → (insertIn x (insertIn y l n₁) n₂ ≡ insertIn y (insertIn x l n₃) n₄)
