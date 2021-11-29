module Logic.Predicate.Equiv where

import      Lvl
open import Logic
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable Obj : Type{ℓ}
private variable Pred : Obj → Stmt{ℓ}

module _ ⦃ _ : Equiv{ℓₑ}(Obj) ⦄ where
  _≡∃_ : ∃{Obj = Obj}(Pred) → ∃{Obj = Obj}(Pred) → Stmt
  [∃]-intro x ≡∃ [∃]-intro y = x ≡ y

  instance
    [≡∃]-reflexivity : Reflexivity(_≡∃_ {Pred = Pred})
    Reflexivity.proof [≡∃]-reflexivity = reflexivity(_≡_)

  instance
    [≡∃]-symmetry : Symmetry(_≡∃_ {Pred = Pred})
    Symmetry.proof [≡∃]-symmetry = symmetry(_≡_)

  instance
    [≡∃]-transitivity : Transitivity(_≡∃_ {Pred = Pred})
    Transitivity.proof [≡∃]-transitivity = transitivity(_≡_)

  instance
    [≡∃]-equivalence : Equivalence(_≡∃_ {Pred = Pred})
    [≡∃]-equivalence = intro

  instance
    [≡∃]-equiv : Equiv{ℓₑ}(∃{Obj = Obj} Pred)
    [≡∃]-equiv = intro(_≡∃_) ⦃ [≡∃]-equivalence ⦄

{- TODO: Replace above with this
open import Functional
open import Structure.Relator.Equivalence.Proofs
∃ₗ-equiv : ∀{ℓ₁ ℓ₂ ℓₑ}{A : Type{ℓ₁}} ⦃ equiv : Equiv{ℓₑ}(A) ⦄ {B : A → Type{ℓ₂}} → Equiv(∃ B)
∃ₗ-equiv ⦃ equiv ⦄ = intro ((_≡_) on₂ [∃]-witness) ⦃ on₂-equivalence{_▫_ = _≡_}{f = [∃]-witness} ⦃ Equiv.equivalence equiv ⦄ ⦄
-}
