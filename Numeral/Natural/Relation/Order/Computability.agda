module Numeral.Natural.Relation.Order.Computability where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Stmt
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Logic.Computability.Binary
open import Functional
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Comparisons.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Relator.Properties

instance
  [≤]-computable : ComputablyDecidable{X = ℕ}(_≤_)
  [≤]-computable = ComputablyDecidable-intro decide ⦃ proof ⦄ where
    decide = (_≤?_)

    proof : ∀{x}{y} → (x ≤ y) ↔ ((x ≤? y) ≡ 𝑇)
    proof{x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
      l : ∀{x}{y} → (x ≤ y) ← ((x ≤? y) ≡ 𝑇)
      l{𝟎}   {_}   ([≡]-intro) = [≤]-minimum
      l{𝐒(x)}{𝟎}   ()
      l{𝐒(x)}{𝐒(y)}(proof)     = [≤]-with-[𝐒] ⦃ l{x}{y}(proof) ⦄

      r : ∀{x}{y} → (x ≤ y) → ((x ≤? y) ≡ 𝑇)
      r{𝟎}   {y}    ([≤]-minimum)      = [≡]-intro
      r{𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = r{x}{y} (proof)

instance
  [≥]-computable : ComputablyDecidable{X = ℕ}(_≥_)
  [≥]-computable = ComputablyDecidable-intro decide ⦃ proof ⦄ where
    decide = (_≥?_)

    proof : ∀{x}{y} → (x ≥ y) ↔ ((x ≥? y) ≡ 𝑇)
    proof{x}{y} = ComputablyDecidable.proof (_≤_) {y}{x}

instance
  [<]-computable : ComputablyDecidable{X = ℕ}(_<_)
  [<]-computable = ComputablyDecidable-intro decide ⦃ proof ⦄ where
    decide = (_<?_)

    proof : ∀{x}{y} → (x < y) ↔ ((x <? y) ≡ 𝑇)
    proof{x}{y} rewrite [<?]-to-[≤?] {x}{y} = ComputablyDecidable.proof (_≤_) {𝐒(x)}{y}

instance
  [>]-computable : ComputablyDecidable{X = ℕ}(_>_)
  [>]-computable = ComputablyDecidable-intro decide ⦃ proof ⦄ where
    decide = (_>?_)

    proof : ∀{x}{y} → (x > y) ↔ ((x >? y) ≡ 𝑇)
    proof{x}{y} = ComputablyDecidable.proof (_<_) {y}{x}

instance
  [≰]-computable : ComputablyDecidable{X = ℕ}(_≰_)
  [≰]-computable = ComputablyDecidable.negation (_≤_)

instance
  [≱]-computable : ComputablyDecidable{X = ℕ}(_≱_)
  [≱]-computable = ComputablyDecidable.negation (_≥_)

instance
  [≮]-computable : ComputablyDecidable{X = ℕ}(_≮_)
  [≮]-computable = ComputablyDecidable.negation (_<_)

instance
  [≯]-computable : ComputablyDecidable{X = ℕ}(_≯_)
  [≯]-computable = ComputablyDecidable.negation (_>_)
