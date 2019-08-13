{-# OPTIONS --with-K #-}

-- The purpose of this module is to allow the BUILTIN EQUALITY pragma while also having module parameters
module Relator.Equals._Eq where

import      Lvl
open import Functional
open import Logic.Propositional
open import Type

-- Definition of equality based on the exact representation of a data structure
-- TODO: Is this called "intensional equality"?
module Internal {ℓ₁}{ℓ₂} where
  infixl 15 _≡_ _≢_
  data _≡_ {T : Type{ℓ₂}} : T → T → Stmt{ℓ₁} where
    instance [≡]-intro : ∀{x : T} → (x ≡ x)
    -- Interpretation:
    --   The only way to construct something of type _≡_ is to have both sides equal.
    --   When matching on the constructor, the type checker "unifies" the two terms,
    --   so that they now are the same object in the type system's eyes.
    --   This is how the builtin pattern matching by [≡]-intro works, //TODO: ...I think
    --   and therefore many propositions for equality becomes "trivial" textually.

  _≢_ : ∀{T : Type{ℓ₂}} → T → T → Stmt{ℓ₁}
  _≢_ a b = ¬(a ≡ b)

open Internal

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE  _≡_ #-}
