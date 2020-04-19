module Structure.Relator.Equivalence where

import      Lvl
open import Logic
open import Logic.Propositional
open import Structure.Relator.Properties
  hiding (reflexivity ; symmetry ; transitivity)
open import Type

-- Definition of an equivalence class
record Equivalence {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_≡_ : T → T → Stmt{ℓ₂}) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
  instance constructor intro
  field
    instance ⦃ reflexivity ⦄  : Reflexivity  (_≡_)
    instance ⦃ symmetry ⦄     : Symmetry     (_≡_)
    instance ⦃ transitivity ⦄ : Transitivity (_≡_)
