module Type.Dependent.PiFunction.Equivalence where

import      DependentFunctional as Fn
open import Logic.Predicate
import      Lvl
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type.Dependent.PiFunction
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable I : Type{ℓ}

module _ {F : I → Type{ℓ}} ⦃ equiv : ∀{i : I} → Equiv{ℓₑ}(F(i)) ⦄ where
  private open module EquivF {i} = Equiv(equiv{i}) using ()

  -- Pointwise equivalence of pi-types (similar to Function.Equals).
  _≡π_ : Π I F → Π I F → Type
  _≡π_ = ∀¹ Fn.∘₂ Fn.pointwise₂,₁(_≡_)

  instance
    [≡π]-reflexivity : Reflexivity(_≡π_)
    [≡π]-reflexivity = intro(reflexivity(_≡_))

  instance
    [≡π]-symmetry : Symmetry(_≡π_)
    [≡π]-symmetry = intro(\p → symmetry(_≡_) p)

  instance
    [≡π]-transitivity : Transitivity(_≡π_)
    [≡π]-transitivity = intro(\p q → transitivity(_≡_) p q)

  product-equiv : Equiv(Π I F)
  Equiv._≡_         product-equiv = _≡π_
  Equiv.equivalence product-equiv = intro
