module Logic.Propositional.Equiv where

import      Lvl
open import Logic
open import Logic.Propositional
import      Logic.Propositional.Theorems as Theorems
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid.WithLvl
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable T A B : Type{ℓ}

instance
  [↔]-reflexivity : Reflexivity{ℓ₂ = ℓ}(_↔_)
  [↔]-reflexivity = intro Theorems.[↔]-reflexivity

instance
  [↔]-symmetry : Symmetry{ℓ₂ = ℓ}(_↔_)
  [↔]-symmetry = intro Theorems.[↔]-symmetry

instance
  [↔]-transitivity : Transitivity{ℓ₂ = ℓ}(_↔_)
  [↔]-transitivity = intro Theorems.[↔]-transitivity

instance
  [↔]-equivalence : Equivalence{ℓ₂ = ℓ}(_↔_)
  [↔]-equivalence = intro

instance
  [↔]-equiv : Equiv(Stmt{ℓ})
  [↔]-equiv = intro(_↔_) ⦃ [↔]-equivalence ⦄
