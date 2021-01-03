module Structure.Relator.Apartness where

import      Lvl
open import Logic
open import Logic.Propositional
open import Structure.Relator.Properties
  hiding (irreflexivity ; symmetry ; cotransitivity)
open import Type

private variable ℓ₁ ℓ₂ : Lvl.Level

-- An apartness relation is a irreflexive, symmetric and cotransitive relation.
record Apartness {T : Type{ℓ₁}} (_#_ : T → T → Stmt{ℓ₂}) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
  instance constructor intro
  field
    instance ⦃ irreflexivity ⦄  : Irreflexivity  (_#_)
    instance ⦃ symmetry ⦄       : Symmetry       (_#_)
    instance ⦃ cotransitivity ⦄ : CoTransitivity (_#_)
