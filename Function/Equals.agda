module Function.Equals where

import      Lvl
open import Functional
import      Function.Names as Names
open import Logic
open import Logic.Propositional
open import Structure.Setoid
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

module Dependent {ℓ₁ ℓ₂ ℓₑ₂} {A : Type{ℓ₁}} {B : A → Type{ℓ₂}} ⦃ equiv-B : ∀{a} → Equiv{ℓₑ₂}(B(a)) ⦄ where
  infixl 15 _⊜_

  -- Function equivalence. When the types and all their values are shared/equivalent.
  record _⊜_ (f : (a : A) → B(a)) (g : (a : A) → B(a)) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓₑ₂} where
    constructor intro
    field
      proof : (f Names.⊜ g)

  instance
    [⊜]-reflexivity : Reflexivity(_⊜_)
    Reflexivity.proof([⊜]-reflexivity) = intro(reflexivity(_≡_) ⦃ Equiv.reflexivity(equiv-B) ⦄)

  instance
    [⊜]-symmetry : Symmetry(_⊜_)
    Symmetry.proof([⊜]-symmetry) (intro fg) = intro(symmetry(_≡_) ⦃ Equiv.symmetry(equiv-B) ⦄ fg)

  instance
    [⊜]-transitivity : Transitivity(_⊜_)
    Transitivity.proof([⊜]-transitivity) (intro fg) (intro gh) = intro(transitivity(_≡_) ⦃ Equiv.transitivity(equiv-B) ⦄ fg gh)

  instance
    [⊜]-equivalence : Equivalence(_⊜_)
    [⊜]-equivalence = record{}

  instance
    [⊜]-equiv : Equiv((a : A) → B(a))
    [⊜]-equiv = intro(_⊜_) ⦃ [⊜]-equivalence ⦄

  instance
    [⊜]-sub : (_≡_) ⊆₂ (_⊜_)
    _⊆₂_.proof [⊜]-sub (intro proof) = intro proof

module _ {ℓ₁ ℓ₂ ℓₑ₂} {A : Type{ℓ₁}} {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  private module D = Dependent {A = A} {B = const B} ⦃ equiv-B ⦄
  open D using (module _⊜_ ; intro) public
  _⊜_              = D._⊜_
  [⊜]-reflexivity  = D.[⊜]-reflexivity
  [⊜]-symmetry     = D.[⊜]-symmetry
  [⊜]-transitivity = D.[⊜]-transitivity
  [⊜]-equivalence  = D.[⊜]-equivalence
  [⊜]-equiv        = D.[⊜]-equiv
  [⊜]-sub          = D.[⊜]-sub
