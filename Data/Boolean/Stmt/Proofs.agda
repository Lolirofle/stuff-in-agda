module Data.Boolean.Stmt.Proofs where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Stmt
open import Type.Properties.MereProposition
open import Structure.Setoid
open import Structure.Relator.Properties

private variable ℓₑ : Lvl.Level
private variable b : Bool

module _ ⦃ equiv : ∀{b} → Equiv{ℓₑ}(IsTrue(b)) ⦄ where
  instance
    IsTrue-prop : MereProposition(IsTrue(b))
    MereProposition.uniqueness (IsTrue-prop{𝑇}) = reflexivity(_≡_) ⦃ Equiv.reflexivity(equiv{𝑇}) ⦄

  instance
    IsFalse-prop : MereProposition(IsFalse(b))
    MereProposition.uniqueness (IsFalse-prop {𝐹}) = reflexivity(_≡_) ⦃ Equiv.reflexivity(equiv{𝑇}) ⦄
