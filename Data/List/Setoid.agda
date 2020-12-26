module Data.List.Setoid where

import      Lvl
open import Data.List
open import Data.List.Equiv
open import Data.List.Relation.Quantification
open import Logic.Propositional
open import Structure.Operator
open import Structure.Setoid.WithLvl
open import Structure.Relator.Equivalence
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Type

private variable ℓ ℓₑ ℓₚ : Lvl.Level
private variable T : Type{ℓ}

instance
  List-equiv : ⦃ Equiv{ℓₑ}(T) ⦄ → Equiv(List(T))
  List-equiv = intro (AllElements₂(_≡_)) ⦃ intro ⦃ intro refl ⦄ ⦃ intro sym ⦄ ⦃ intro trans ⦄ ⦄ where
    refl : Names.Reflexivity(AllElements₂(_≡_))
    refl{∅}     = ∅
    refl{x ⊰ l} = reflexivity(_≡_) ⊰ refl{l}

    sym : Names.Symmetry(AllElements₂(_≡_))
    sym ∅        = ∅
    sym (p ⊰ ps) = symmetry(_≡_) p ⊰ sym ps

    trans : Names.Transitivity(AllElements₂(_≡_))
    trans ∅        ∅        = ∅
    trans (p ⊰ ps) (q ⊰ qs) = (transitivity(_≡_) p q) ⊰ (trans ps qs)

instance
  List-equiv-extensionality : ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → Extensionality(List-equiv ⦃ equiv ⦄)
  List-equiv-extensionality ⦃ equiv ⦄ = intro ⦃ binaryOperator = intro(_⊰_) ⦄ (\{(p ⊰ _) → p}) (\{(_ ⊰ pl) → pl}) \()
