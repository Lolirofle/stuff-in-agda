module Numeral.Natural.Prime.Proofs.Product where

import      Lvl
open import Data.Either as Either using ()
open import Functional
open import Lang.Instance
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Oper
open import Numeral.Natural.Prime
open import Numeral.Natural.Relation.Divisibility.Proofs.Product
open import Sets.PredicateSet renaming (_≡_ to _≡ₛ_)
open import Type

private variable a b : ℕ

-- The prime factors of a product is the prime factors of its factors.
product-primeFactors : PrimeFactor(a ⋅ b) ≡ₛ (PrimeFactor(a) ∪ PrimeFactor(b))
product-primeFactors = [↔]-intro l r where
  l : PrimeFactor(a ⋅ b) ⊇ (PrimeFactor(a) ∪ PrimeFactor(b))
  l{a}{b}{x} (Either.Left  intro) = intro ⦃ factor = divides-with-[⋅] {x}{a}{b} ([∨]-introₗ infer) ⦄
  l{a}{b}{x} (Either.Right intro) = intro ⦃ factor = divides-with-[⋅] {x}{a}{b} ([∨]-introᵣ infer) ⦄

  r : PrimeFactor(a ⋅ b) ⊆ (PrimeFactor(a) ∪ PrimeFactor(b))
  r{a}{b}{x} intro = Either.map (p ↦ intro ⦃ factor = p ⦄) (p ↦ intro ⦃ factor = p ⦄) (prime-divides-of-[⋅] {x}{a}{b} infer infer)
