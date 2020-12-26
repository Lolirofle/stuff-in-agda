module Relator.Equals where

open import Logic
import      Lvl
open import Type
open import Type.Cubical
open import Type.Cubical.Path
open import Type.Cubical.Path.Proofs


infix 15 _≡_

_≡_ = Path

-- _≢_ : ∀{ℓ}{T} → T → T → Stmt{ℓ}
-- _≢_ a b = ¬(a ≡ b)

{-# BUILTIN REWRITE  _≡_ #-}

data Id {ℓ}{T : Type{ℓ}} : T → T → Stmt{ℓ} where
  instance intro : ∀{x : T} → (Id x x)

{-# BUILTIN EQUALITY Id #-}
