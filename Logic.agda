module Logic {ℓ} where

Stmt : _
Stmt = Set(ℓ)

open import Agda.Primitive public
  renaming (Setω to Stmtω)
