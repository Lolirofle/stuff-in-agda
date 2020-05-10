module Logic.Predicate.Equiv where

import      Lvl
open import Logic
open import Logic.Predicate
open import Structure.Setoid.WithLvl
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable X : Type{ℓ}
private variable P : X → Stmt{ℓ}

module _ ⦃ _ : Equiv{ℓₑ}(X) ⦄ where
  _≡∃_ : ∃{Obj = X}(P) → ∃{Obj = X}(P) → Stmt
  [∃]-intro x ≡∃ [∃]-intro y = x ≡ y

  instance
    [≡∃]-reflexivity : Reflexivity(_≡∃_ {P = P})
    Reflexivity.proof [≡∃]-reflexivity = reflexivity(_≡_)

  instance
    [≡∃]-symmetry : Symmetry(_≡∃_ {P = P})
    Symmetry.proof [≡∃]-symmetry = symmetry(_≡_)

  instance
    [≡∃]-transitivity : Transitivity(_≡∃_ {P = P})
    Transitivity.proof [≡∃]-transitivity = transitivity(_≡_)

  instance
    [≡∃]-equivalence : Equivalence(_≡∃_ {P = P})
    [≡∃]-equivalence = intro

  instance
    [≡∃]-equiv : Equiv{ℓₑ}(∃{Obj = X} P)
    [≡∃]-equiv = intro(_≡∃_) ⦃ [≡∃]-equivalence ⦄
