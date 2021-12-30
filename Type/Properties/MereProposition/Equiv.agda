module Type.Properties.MereProposition.Equiv where

import      Lvl
open import Type.Properties.MereProposition
open import Structure.Relator.Properties
open import Structure.Relator.Proofs
open import Structure.Relator
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

module _
  ⦃ equiv : Equiv{ℓₑ}(T) ⦄
  ⦃ prop : MereProposition(T) ⦄
  (_▫_ : T → T → Type{ℓ})
  ⦃ rel : BinaryRelator(_▫_) ⦄
  ⦃ refl : Reflexivity(_▫_) ⦄
  where

  prop-refl-global-rel : ∀{x y} → (x ▫ y)
  prop-refl-global-rel = sub₂(_≡_)(_▫_) ⦃ reflexive-rel-sub ⦄ (uniqueness(T))    
