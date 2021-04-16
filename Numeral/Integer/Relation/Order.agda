module Numeral.Integer.Relation.Order where

open import Functional
import      Lvl
import      Numeral.Natural.Relation.Order as ℕ
open import Numeral.Integer
open import Numeral.Integer.Oper
open import Relator.Ordering
open import Type

-- Inequalities/Comparisons
data _≤_ : ℤ → ℤ → Type{Lvl.𝟎} where
  neg-neg : ∀{a b} → (a ℕ.≤ b) → (−𝐒ₙ(b)) ≤ (−𝐒ₙ(a))
  neg-pos : ∀{a b} → (−𝐒ₙ(a)) ≤ (+ₙ b)
  pos-pos : ∀{a b} → (a ℕ.≤ b) → (+ₙ a)   ≤ (+ₙ b)

_<_ : ℤ → ℤ → Type
_<_ = (_≤_) ∘ 𝐒

open From-[≤][<] (_≤_)(_<_) public

module _ where
  open import Structure.Relator.Properties

  instance
    [≤][−𝐒ₙ]-sub : (swap(_≤_) on₂ (−𝐒ₙ_)) ⊆₂ (ℕ._≤_)
    _⊆₂_.proof [≤][−𝐒ₙ]-sub (neg-neg p) = p

  instance
    [≤][+ₙ]-sub : ((_≤_) on₂ (+ₙ_)) ⊆₂ (ℕ._≤_)
    _⊆₂_.proof [≤][+ₙ]-sub (pos-pos p) = p
