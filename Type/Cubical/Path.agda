module Type.Cubical.Path where

open import Logic
open import Type
open import Type.Cubical

postulate PathP : ∀{ℓ}(P : Interval → Stmt{ℓ}) → P(Interval.𝟎) → P(Interval.𝟏) → Stmt{ℓ}
{-# BUILTIN PATHP PathP #-}

-- The type of paths.
-- Can be seen as a path in some space (TODO: What space? P?)
-- (A continuous function from the closed unit interval to the space).
Path : ∀{ℓ}{P : Type{ℓ}} → P → P → Type{ℓ}
Path {P = P} = PathP(\i → P)
{-# BUILTIN PATH Path #-}
