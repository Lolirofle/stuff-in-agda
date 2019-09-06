{-# OPTIONS --rewriting #-}

module Relator.Equals where

import      Lvl
open import Logic
open import Logic.Propositional
open import Functional
open import Type

infixl 15 _≡_ _≢_

-- Definition of intensional equality.
-- Also called "identical".
-- Two terms are equal when data representation is the same.
data _≡_ {ℓ}{T : Type{ℓ}} : T → T → Stmt{ℓ} where
  instance [≡]-intro : ∀{x : T} → (x ≡ x)
  -- Interpretation:
  --   The only way to construct something of type _≡_ is to have both sides equal.
  --   When matching on the constructor, the type checker "unifies" the two terms,
  --   so that they now are the same object in the type system's eyes.
  --   This is how the builtin pattern matching by [≡]-intro works, //TODO: ...I think
  --   and therefore many propositions for equality becomes "trivial" textually.

_≢_ : ∀{ℓ}{T} → T → T → Stmt{ℓ}
_≢_ a b = ¬(a ≡ b)

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE  _≡_ #-}
