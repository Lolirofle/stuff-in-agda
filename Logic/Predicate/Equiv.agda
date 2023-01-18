module Logic.Predicate.Equiv where

open import Functional
import      Lvl
open import Logic
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Setoid.On₂
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable Obj : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(Obj) ⦄ where
  private variable Pred : Obj → Stmt{ℓ}

  -- Equivalence on the object of the existential (meaning the predicate "becomes proof-irrelevant").
  instance
    [≡∃]-equiv : Equiv{ℓₑ}(∃{Obj = Obj} Pred)
    [≡∃]-equiv = on₂-equiv [∃]-witness

  module _ (let _ = Pred) where
    open Equiv([≡∃]-equiv {Pred = Pred}) public
      using()
      renaming (
        _≡_          to _≡∃_ ;
        reflexivity  to [≡∃]-reflexivity ;
        symmetry     to [≡∃]-symmetry ;
        transitivity to [≡∃]-transitivity ;
        equivalence  to [≡∃]-equivalence
      )
