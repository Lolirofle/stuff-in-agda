module Numeral.Natural.Relation.Divisibility.Proofs.Productₗ where

open import Functional
open import Logic.Propositional.Equiv
open import Numeral.Natural
open import Numeral.Natural.Coprime
open import Numeral.Natural.Function.LeastCommonMultiple.Proofs
open import Numeral.Natural.Oper as ℕ
open import Numeral.Natural.Relation.Divisibility as ℕ
open import Numeral.Natural.Function.LeastCommonMultiple
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator

private variable a b c : ℕ

divides-with-[⋅]ₗ : Coprime a b → (a ∣ c) → (b ∣ c) → ((a ⋅ b) ∣ c)
divides-with-[⋅]ₗ {a}{b}{𝟎} _ _ _ = Div𝟎
divides-with-[⋅]ₗ {a}{b}{c@(𝐒 _)} coprim = substitute₂-₁ᵣ(_∣_)(_) ([⋅]-lcm-coprim coprim) ∘₂ Lcm.minimum₂ (Lcm-lcm{a}{b}) {c}
