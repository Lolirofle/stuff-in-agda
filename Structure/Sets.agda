module Structure.Sets where

open import Functional
open import Lang.Instance
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid.WithLvl
open import Structure.Sets.Relator
open import Type

private variable ℓ ℓₑ ℓₗ : Lvl.Level
private variable S E : Type{ℓ}

module _ ⦃ equiv-S : let _ = E ; _ = S ; _ = ℓₗ in Equiv{ℓₑ}(S) ⦄ where
  module _ (_∈_ : E → S → Stmt{ℓₗ}) where
    SetExtensionality = SetEqualityRelation(_∈_)(_∈_) (Equiv._≡_ equiv-S)
    module SetExtensionality = SetEqualityRelation{_∈ₗ_ = _∈_}{_∈ᵣ_ = _∈_}{_≡_ = Equiv._≡_ equiv-S}
    set-extensionality = inst-fn SetExtensionality.membership

  module _ (setExt : ∃(SetExtensionality)) where
    open ∃(setExt) using () renaming (witness to _∈_) public

    _∋_ : S → E → Stmt
    _∋_ = swap(_∈_)

    _∉_ : E → S → Stmt
    _∉_ = (¬_) ∘₂ (_∈_)
