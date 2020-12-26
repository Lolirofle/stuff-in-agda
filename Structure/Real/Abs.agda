open import Logic.Classical
open import Structure.Real

module Structure.Real.Abs {ℓ₁ ℓ₂ ℓₑ} {R} ⦃ R-equiv ⦄ (_+_) (_⋅_) (_≤_) ⦃ classical : ∀{ℓ}{P} → Classical{ℓ}(P) ⦄ ⦃ reals : RealTheory{ℓ₁}{ℓₑ}{ℓ₂} {R} ⦃ R-equiv ⦄ (_+_)(_⋅_)(_≤_) ⦄ where
open RealTheory(reals)

open import Data.Boolean
import      Lvl
open import Functional
open import Logic
open import Logic.Classical
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Operator.Field
open import Structure.Operator.Monoid
open import Structure.Operator.Group
open import Structure.Relator.Ordering
open        Structure.Relator.Ordering.Weak.Properties
open import Structure.Relator.Properties
open import Syntax.Type
open import Type

-- TODO: This file is probably redundant. Move this to Structure.Operator.OrderedField.Abs

-- TODO: Prove somewhere that: (P → ([∨]-elim x y (_ :of: (P ∨ Q)) ≡ x)) ∧ (Q → ([∨]-elim x y (_ :of: (P ∨ Q)) ≡ y)) because this is neccessary when proving the properties of abs

-- abs : R → R
-- abs(x) = if(decide{P = x ≤ 𝟎}) then (− x) else x

