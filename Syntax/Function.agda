module Syntax.Function where

import Lvl

-- Custom syntax for anonymous functions/mappings
[↦] : ∀{ℓ}{T : Set(ℓ)} → T → T
[↦] x = x
infix 2 [↦]
syntax [↦](λ x → y) = x ↦ y
{-# DISPLAY [↦] x = x #-}
