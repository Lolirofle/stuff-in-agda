module String.Decidable where

open import Char
open import Char.Decidable
open import Data.List.Decidable as List
open import Data.List.Equiv.Id
open import Data.List
open import Functional
open import Logic.Predicate
open import Logic.Propositional
open import Operator.Equals
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import String
import      String.Functions as String
open import String.Proofs
open import Structure.Function
open import Structure.Function.Domain
open import Type.Properties.Decidable
open import Type.Properties.Decidable.Proofs

instance
  String-decidable-equiv : EquivDecidable(String)
  ∃.witness String-decidable-equiv = (_==_) on₂ String.chars
  ∃.proof   String-decidable-equiv = on₂-bool-decider{_▫₁_ = _≡_}{_▫₂_ = _≡_}
    ([↔]-intro (congruence₁(String.chars)) (injective(String.chars)))
    (List.[≡]-decider ⦃ dec = [∃]-proof Char-decidable-equiv ⦄)
