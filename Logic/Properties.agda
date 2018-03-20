module Logic.Properties{ℓ} where

open import Logic.Propositional{ℓ}

-- A proposition which is either provable or unprovable.
-- This could then be interpreted as true or false.
-- Also called: Decidable
record Classical (φ : Stmt) : Stmt where
  instance constructor classical
  field
    ⦃ proof ⦄ : φ ∨ (¬ φ)
