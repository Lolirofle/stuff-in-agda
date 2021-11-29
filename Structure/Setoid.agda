module Structure.Setoid {ℓₑ ℓₒ} where

import Lvl
open import Functional.Dependent
open import Functional.Instance
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Relator.Equivalence
open import Syntax.Function
import      Type

module _ where
  open Type

  -- An instance of `Equiv(T)` is that the type `T` has an equivalence relation which may be treated as a default one.
  -- Helps finding an instance of an equivalence relation for a type.
  record Equiv (T : Type{ℓₒ}) : Type{Lvl.𝐒(ℓₑ) Lvl.⊔ ℓₒ} where
    constructor intro

    infixl 15 _≡_ _≢_
    field
      _≡_ : T → T → Type{ℓₑ}

    field
      instance ⦃ equivalence ⦄ : Equivalence(_≡_)

    _≢_ : T → T → Type{ℓₑ}
    a ≢ b = ¬(a ≡ b)

    open Equivalence(equivalence) public

  open Equiv ⦃ ... ⦄ using (_≡_ ; _≢_) renaming (equivalence to Equiv-equivalence) public
  {-# INLINE _≡_ #-} -- TODO: Not sure if this does anything
  {-# DISPLAY Equiv._≡_ a b = a ≡ b #-} -- TODO: Not sure about this either

module _ where
  -- A set and an equivalence relation on it
  Setoid = ∃(Equiv)
  module Setoid(([∃]-intro T ⦃ equiv-T ⦄) : Setoid) where
    Type : Type.Type
    Type = T
    open Equiv(equiv-T) public
