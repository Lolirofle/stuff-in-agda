module Logic{ℓ} where

-- open import Logic
-- open import Logic.Classical

-- Everything is computably decidable
-- instance postulate classical : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P)

Stmt : _
Stmt = Set(ℓ) -- Prop(ℓ)

open import Agda.Primitive public
  renaming (Setω to Stmtω)
