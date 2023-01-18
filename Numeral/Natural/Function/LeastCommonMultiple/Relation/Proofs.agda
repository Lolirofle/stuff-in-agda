module Numeral.Natural.Function.LeastCommonMultiple.Relation.Proofs where

open import Functional
open import Numeral.Natural
open import Numeral.Natural.Oper as ℕ
open import Numeral.Natural.Function.LeastCommonMultiple
open import Numeral.Natural.Relation.Divisibility as ℕ
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator.Properties
open import Structure.Setoid.Uniqueness

private variable a b c : ℕ

Lcm-unique : Unique(Lcm a b)
Lcm-unique abx aby = antisymmetry(ℕ._∣_)(_≡_)
  (Lcm.minimum₂ abx (Lcm.multipleₗ aby) (Lcm.multipleᵣ aby))
  (Lcm.minimum₂ aby (Lcm.multipleₗ abx) (Lcm.multipleᵣ abx))

Lcm-zero : Lcm 0 0 0
Lcm-zero = Lcm.intro₂ Div𝟎 Div𝟎 (const id)

Lcm-absorberₗ : Lcm 0 b 0
Lcm-absorberₗ = Lcm.intro₂ Div𝟎 Div𝟎 const

Lcm-absorberᵣ : Lcm a 0 0
Lcm-absorberᵣ = Lcm.intro₂ Div𝟎 Div𝟎 (const id)

Lcm-identityₗ : Lcm 1 b b
Lcm-identityₗ = Lcm.intro₂ [1]-divides (reflexivity(_∣_)) (const id)

Lcm-identityᵣ : Lcm a 1 a
Lcm-identityᵣ = Lcm.intro₂ (reflexivity(_∣_)) [1]-divides const
