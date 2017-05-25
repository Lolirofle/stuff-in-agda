module Relator.Bijection {l₁} {l₂} where

import      Level as Lvl
open import Functional
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Structure.Function.Domain{l₁}{l₂}
open import Structure.Relator.Properties {l₁} {l₂}
open import Type{l₂}

-- TODO: Same as ∃f. Bijective(f)
data Bijection (T₁ : Type) (T₂ : Type) : Stmt where
  bijection-intro : (f : T₁ → T₂) → Bijective(f) → Bijection(T₁)(T₂)

-- TODO: Depends on Bijective(id), which I have not proved yet
-- instance
--   Bijection-reflexivity : Reflexivity(Bijection)
--   Bijection-reflexivity = bijection-intro(id)([∧]-intro()())

-- TODO: This gives the same error I get when proving Bijective(id). Something is wrong with the level stuff I use
-- instance
--   Bijection-symmetry : ∀{T} → Symmetry(Bijection)
--   Bijection-symmetry(proof) = proof

-- TODO: Use function composition in some way
-- instance
--   Bijection-transitivity : ∀{T} → Transitivity(Bijection)
--   Bijection-transitivity([∧]-intro [≡]-intro [≡]-intro) = [≡]-intro
