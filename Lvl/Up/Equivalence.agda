module Lvl.Up.Equivalence where

open import Functional
import      Functional.Categorical as C
open import Lvl
open import Structure.Setoid
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

instance
  LvlUp-equiv : ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → Equiv(Lvl.Up{ℓ}(T))
  Equiv._≡_ (LvlUp-equiv {ℓ = ℓ}) (up x) (up y) = Lvl.Up{ℓ}(x ≡ y)
  Equivalence.reflexivity  (Equiv.equivalence LvlUp-equiv) = intro(Lvl.up(reflexivity(_≡_)))
  Equivalence.symmetry     (Equiv.equivalence LvlUp-equiv) = intro(Lvl.up ∘ symmetry(_≡_) ∘ Lvl.Up.obj)
  Equivalence.transitivity (Equiv.equivalence LvlUp-equiv) = intro(C.on₂(_≡_)((_≡_) on₂ Up.obj) (Lvl.up ∘₂ transitivity(_≡_)) Lvl.Up.obj)
