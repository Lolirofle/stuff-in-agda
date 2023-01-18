module Numeral.Natural.Relation.ModuloCongruence where

open import Functional
open import Numeral.Natural
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Relation
open import Relator.Equals
open import Type

private variable m n x y : ℕ

[mod_]_≡_ : (m : ℕ) → .⦃ pos : Positive(m) ⦄ → ℕ → ℕ → Type
[mod m ] a ≡ b = ((_≡_) on₂ (_mod m)) a b

_≡_[mod_] : ℕ → ℕ → (m : ℕ) → .⦃ pos : Positive(m) ⦄ → Type
a ≡ b [mod m ] = [mod m ] a ≡ b
