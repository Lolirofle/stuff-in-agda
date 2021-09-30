module Type.Identity where

import      Lvl
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

-- Identity type.
-- Also called: Propositional equality.
-- Two terms are identical/equal when their data representation are the same.
data Id {T : Type{ℓ}} : T → T → Type{ℓ} where
  instance intro : ∀{x : T} → Id x x
  -- Interpretation:
  --   The only way to construct something of type Id is to use identical objects for both arguments.
  --   When matching on the constructor, the type checker "unifies" the two terms making them the same.
  --   This is how the builtin pattern matching by intro works and how identity proofs become "trivial" syntactically.

{-# BUILTIN EQUALITY Id #-}
{-# BUILTIN REWRITE  Id #-}

elim : (P : ∀{x y : T} → (Id x y) → Type{ℓ}) → (∀{x} → P(intro{x = x})) → (∀{x y} → (eq : (Id x y)) → P(eq))
elim _ p intro = p
