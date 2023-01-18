module Structure.Relator.Apartness where

import      Lvl
open import Logic
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Relator.Properties
  hiding (irreflexivity ; symmetry ; cotransitivity)
open import Type

private variable ℓ₁ ℓ₂ : Lvl.Level

-- An apartness relation is a irreflexive, symmetric and cotransitive relation.
record Apartness {T : Type{ℓ₁}} (_#_ : T → T → Stmt{ℓ₂}) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
  constructor intro
  field
    ⦃ irreflexivity ⦄  : Irreflexivity  (_#_)
    ⦃ symmetry ⦄       : Symmetry       (_#_)
    ⦃ cotransitivity ⦄ : CoTransitivity (_#_)

Apart : ∀{ℓₑ ℓ : Lvl.Level} → Type{ℓ} → Type
Apart{ℓₑ}(T) = ∃(Apartness{ℓ₂ = ℓₑ}{T = T})
module Apart {ℓ ℓₑ : Lvl.Level} {T : Type{ℓ}} (apart : Apart{ℓₑ}(T)) where
  _#_ = [∃]-witness apart
  apartness = [∃]-proof apart
  open Apartness(apartness) public
open Apart ⦃ ... ⦄ using (_#_) public
