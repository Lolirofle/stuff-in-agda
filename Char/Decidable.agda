module Char.Decidable where

open import Char
open import Char.Functions
open import Char.Proofs
open import Functional
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Natural.Decidable as ℕ
open import Operator.Equals
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
open import Type.Properties.Decidable.Proofs

-- TODO: ((ℕ._≡?_) on₂ unicodeCodePoint) is used here because it works. Char._≡?_ should be prefered, but it seems unprovable
instance
  Char-decidable-equiv : EquivDecidable(Char)
  ∃.witness Char-decidable-equiv = (_==_) on₂ unicodeCodePoint
  ∃.proof   Char-decidable-equiv {x}{y} = on₂-bool-decider{_▫₁_ = _≡_}{_▫₂_ = _≡_}
    ([↔]-intro (congruence₁(unicodeCodePoint)) (injective(unicodeCodePoint)))
    ℕ.[≡?]-decider
