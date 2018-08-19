module Numeral.Natural.Relation.Order.Computability{ℓ} where

import      Lvl
open import Data.Boolean
open import Data.Boolean.AsSet
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Logic.Computability.Binary{ℓ}{Lvl.𝟎}
open import Functional
open import Logic.Propositional{ℓ}
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Relation.Order{ℓ}
open import Numeral.Natural.Relation.Order.Proofs{ℓ}
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Relator.Properties

instance
  [≤]-computable : ComputablyDecidable{ℕ}(_≤_)
  [≤]-computable = ComputablyDecidable-intro decide ⦃ proof ⦄ where
    decide = (_≤?_)

    proof : ∀{x}{y} → (x ≤ y) ↔ ((x ≤? y) ≡ 𝑇)
    proof{x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
      l : ∀{x}{y} → (x ≤ y) ← ((x ≤? y) ≡ 𝑇)
      l{𝟎}   {_}   ([≡]-intro) = [≤][0]ᵣ-minimum
      l{𝐒(x)}{𝟎}   ()
      l{𝐒(x)}{𝐒(y)}(proof)     = [≤]-with-[𝐒] ⦃ l{x}{y}(proof) ⦄

      r : ∀{x}{y} → (x ≤ y) → ((x ≤? y) ≡ 𝑇)
      r{𝟎}   {y}    ([≤][0]ᵣ-minimum)      = [≡]-intro
      r{𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = r{x}{y} (proof)

instance -- TODO: Is it possible to reuse the proof of [≤]-computable?
  [≥]-computable : ComputablyDecidable{ℕ}(_≥_)
  [≥]-computable = ComputablyDecidable-intro decide ⦃ proof ⦄ where
    decide = (_≥?_)

    proof : ∀{x}{y} → (x ≥ y) ↔ ((x ≥? y) ≡ 𝑇)
    proof{x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
      l : ∀{x}{y} → (x ≥ y) ← ((x ≥? y) ≡ 𝑇)
      l{_}   {𝟎}   ([≡]-intro) = [≤][0]ᵣ-minimum
      l{𝟎}   {𝐒(y)}()
      l{𝐒(x)}{𝐒(y)}(proof)     = [≤]-with-[𝐒] ⦃ l{x}{y}(proof) ⦄

      r : ∀{x}{y} → (x ≥ y) → ((x ≥? y) ≡ 𝑇)
      r{x}   {𝟎}    ([≤][0]ᵣ-minimum)      = [≡]-intro
      r{𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = r{x}{y} (proof)

-- TODO: [<]-computable
-- TODO: [>]-computable
