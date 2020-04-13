module Sets.Setoid.WithLvl where

import Lvl
open import Functional.Dependent
open import Lang.Instance
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties using (Reflexivity ; Symmetry ; Transitivity)
open import Syntax.Function
import      Type

private variable ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ : Lvl.Level

module EquivInnerModule {ℓₗ ℓₒ} where
  module _ where
    open Type

    -- An instance of `Equiv(T)` is that the type `T` has an equivalence relation which may be treated as a default one.
    -- Helps finding an instance of an equivalence relation for a type.
    record Equiv (T : Type{ℓₒ}) : Type{Lvl.𝐒(ℓₗ) ⊔ ℓₒ} where
      constructor intro

      infixl 15 _≡_ _≢_
      field
        _≡_ : T → T → Type{ℓₗ}

      field
        instance ⦃ [≡]-equivalence ⦄ : Equivalence(_≡_)

      _≢_ : T → T → Type{ℓₗ}
      a ≢ b = ¬(a ≡ b)

      open Equivalence([≡]-equivalence) public

    open Equiv ⦃ ... ⦄ using (_≡_ ; _≢_ ; [≡]-equivalence) public
    {-# INLINE _≡_ #-}
    {-# DISPLAY Equiv._≡_ a b = a ≡ b #-}

  -- A set and an equivalence relation on it
  Setoid : Type.Type
  Setoid = ∃(Equiv)
  module Setoid(setoid : Setoid) where
    Type : Type.Type
    Type = [∃]-witness setoid
    open Equiv([∃]-proof setoid) public

open EquivInnerModule hiding (intro) public
