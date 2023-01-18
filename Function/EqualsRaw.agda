module Function.EqualsRaw where

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Structure.Setoid
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

-- TODO: Try to use this module instead of Function.Equals

module Dependent {ℓ₁ ℓ₂ ℓₑ₂} {A : Type{ℓ₁}} {B : A → Type{ℓ₂}} ⦃ equiv-B : ∀{a} → Equiv{ℓₑ₂}(B(a)) ⦄ where
  import Function.Names
  _⊜_ = Function.Names._⊜_ ⦃ \{a} → equiv-B{a} ⦄

  instance
    [⊜]-reflexivity : Reflexivity(_⊜_)
    Reflexivity.proof([⊜]-reflexivity) = reflexivity(_≡_) ⦃ Equiv.reflexivity(equiv-B) ⦄

  instance
    [⊜]-symmetry : Symmetry(_⊜_)
    Symmetry.proof([⊜]-symmetry) fg = symmetry(_≡_) ⦃ Equiv.symmetry(equiv-B) ⦄ fg

  instance
    [⊜]-transitivity : Transitivity(_⊜_)
    Transitivity.proof([⊜]-transitivity) fg gh = transitivity(_≡_) ⦃ Equiv.transitivity(equiv-B) ⦄ fg gh

  instance
    [⊜]-equivalence : Equivalence(_⊜_)
    [⊜]-equivalence = record{}

  instance
    [⊜]-equiv : Equiv((a : A) → B(a))
    [⊜]-equiv = intro(_⊜_) ⦃ [⊜]-equivalence ⦄

  instance
    [⊜]-sub : (_≡_) ⊆₂ (_⊜_)
    [⊜]-sub = intro id

module _ {ℓ₁ ℓ₂ ℓₑ₂} {A : Type{ℓ₁}} {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  private module D = Dependent {A = A} {B = const B} ⦃ equiv-B ⦄
  _⊜_              = D._⊜_
  [⊜]-reflexivity  = D.[⊜]-reflexivity
  [⊜]-symmetry     = D.[⊜]-symmetry
  [⊜]-transitivity = D.[⊜]-transitivity
  [⊜]-equivalence  = D.[⊜]-equivalence
  [⊜]-equiv        = D.[⊜]-equiv
  [⊜]-sub          = D.[⊜]-sub
