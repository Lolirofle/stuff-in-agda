open import Logic.Classical
open import Structure.Real

module Structure.Real.Abs {ℓ₁ ℓ₂} {R} ⦃ R-equiv ⦄ (_+_) (_⋅_) (_≤_) ⦃ classical : ∀{ℓ}{P} → Classical{ℓ}(P) ⦄ ⦃ reals : RealTheory{ℓ₁}{ℓ₂} {R} ⦃ R-equiv ⦄ (_+_)(_⋅_)(_≤_) ⦄ where
open RealTheory(reals)

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid
open import Structure.Operator.Field
open import Structure.Operator.Monoid
open import Structure.Operator.Group
open import Structure.Relator.Ordering
open        Structure.Relator.Ordering.Weak.Properties
open import Type

-- TODO: Prove somewhere that: (P → ([∨]-elim x y (_ :of: (P ∨ Q)) ≡ x)) ∧ (Q → ([∨]-elim x y (_ :of: (P ∨ Q)) ≡ y)) because this is neccessary when proving the properties of abs

{-
abs : R → R
abs(x) = [∨]-elim (const(− x)) (const(x)) (excluded-middle{P = x ≤ 𝟎})

module Proofs where
  postulate abs-of-positive : ∀{x} → ⦃ _ : (𝟎 ≤ x)⦄ → (abs(x) ≡ x)
  postulate abs-of-negative : ∀{x} → ⦃ _ : (x ≤ 𝟎)⦄ → (abs(x) ≡ − x)
  postulate abs-positive : ∀{x} → (𝟎 ≤ abs(x))
-}
