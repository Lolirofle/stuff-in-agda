module Logic {ℓ} where

Stmt : _
Stmt = Set(ℓ)

open import Agda.Primitive public
  using ()
  renaming (Setω to Stmtω)
