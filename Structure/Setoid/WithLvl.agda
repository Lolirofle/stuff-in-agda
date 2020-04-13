module Structure.Setoid.WithLvl {ℓₗ ℓₒ} where

import Lvl
open import Functional.Dependent
open import Lang.Instance
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Relator.Equivalence
open import Syntax.Function
import      Type

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
      instance ⦃ equivalence ⦄ : Equivalence(_≡_)

    _≢_ : T → T → Type{ℓₗ}
    a ≢ b = ¬(a ≡ b)

    open Equivalence(equivalence) public

  open Equiv ⦃ ... ⦄ using (_≡_ ; _≢_) renaming (equivalence to Equiv-equivalence) public
  {-# INLINE _≡_ #-}
  {-# DISPLAY Equiv._≡_ a b = a ≡ b #-}

module _ where
  -- A set and an equivalence relation on it
  Setoid = ∃(Equiv)
  module Setoid(([∃]-intro T ⦃ equiv ⦄) : Setoid) where
    Type : Type.Type
    Type = T
    open Equiv(equiv) public