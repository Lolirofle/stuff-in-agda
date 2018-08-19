module Numeral.Natural.Relation.Computability{ℓ} where

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
open import Relator.Equals
open import Relator.Equals.Proofs

instance
  [≡]-computable : ComputablyDecidable{ℕ}(_≡_)
  [≡]-computable = ComputablyDecidable-intro decide ⦃ proof ⦄ where
    decide = (_≡?_)

    proof : ∀{x}{y} → (x ≡ y) ↔ ((x ≡? y) ≡ 𝑇)
    proof{x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
      l : ∀{x}{y} → (x ≡ y) ← ((x ≡? y) ≡ 𝑇)
      l{𝟎}   {𝟎}   ([≡]-intro) = [≡]-intro
      l{𝟎}   {𝐒(_)}()
      l{𝐒(_)}{𝟎}   ()
      l{𝐒(x)}{𝐒(y)}(proof) = [≡]-with(𝐒) (l{x}{y}(proof))

      r : ∀{x}{y} → (x ≡ y) → ((x ≡? y) ≡ 𝑇)
      r{𝟎}   {𝟎}    ([≡]-intro) = [≡]-intro
      r{𝟎}   {𝐒(_)} ()
      r{𝐒(_)}{𝟎}    ()
      r{𝐒(x)}{𝐒(.x)}([≡]-intro) = r{x}{x}([≡]-intro)

instance
  [≢]-computable : ComputablyDecidable{ℕ}(_≢_)
  [≢]-computable = ComputablyDecidable-intro decide ⦃ proof ⦄ where
    decide = (_≢?_)

    postulate proof : ∀{x}{y} → (x ≢ y) ↔ ((x ≢? y) ≡ 𝑇)
