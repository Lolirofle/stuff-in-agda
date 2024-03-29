module Data.Proofs where

import      Lvl
open import Data
open import Logic
open import Logic.Propositional
open import Structure.Setoid renaming (_≡_ to _≡ₛ_)
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type
open import Type.Properties.Empty using (IsEmpty ; intro)
open import Type.Properties.Singleton

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ ℓ₁ ℓ₂ ℓₒᵤₜ : Lvl.Level
private variable T : Type{ℓ}

module _ (_▫_ : Empty{ℓ} → Empty{ℓ} → Stmt{ℓₑ}) where
  Empty-equiv : Equiv(Empty)
  Equiv._≡_ Empty-equiv = _▫_
  Reflexivity.proof  (Equivalence.reflexivity  (Equiv.equivalence Empty-equiv)) {}
  Symmetry.proof     (Equivalence.symmetry     (Equiv.equivalence Empty-equiv)) {}
  Transitivity.proof (Equivalence.transitivity (Equiv.equivalence Empty-equiv)) {}

-- Any binary relation on Unit is an equivalence given that it is reflexive.
module _ (_▫_ : Unit{ℓ} → Unit{ℓ} → Stmt{ℓ}) ⦃ proof : (<> ▫ <>) ⦄ where
  Unit-equiv : Equiv(Unit)
  Equiv._≡_ Unit-equiv = (_▫_)
  Reflexivity.proof  (Equivalence.reflexivity  (Equiv.equivalence Unit-equiv))       = proof
  Symmetry.proof     (Equivalence.symmetry     (Equiv.equivalence Unit-equiv)) _     = proof
  Transitivity.proof (Equivalence.transitivity (Equiv.equivalence Unit-equiv)) _ _   = proof

module _ where
  open import Type.Identity

  instance
    Empty-Id-equiv : Equiv(Empty{ℓ})
    Empty-Id-equiv = Empty-equiv(Id)

  instance
    Unit-Id-equiv : Equiv(Unit{ℓ})
    Unit-Id-equiv = Unit-equiv(Id)

  {- TODO: So, why is this unprovable but Unit-IsUnit is? UIP? What is the difference?
  module _ where
    open import Relator.Equals.Proofs.Equiv
    testee : ∀{T : Type{ℓ}}{a : T} → IsUnit{ℓ}(a ≡ a)
    IsUnit.unit       testee     = [≡]-intro
    IsUnit.uniqueness testee {x} = {!!}
  -}

instance
  -- `Unit` is an unit type.
  Unit-IsUnit : ⦃ equiv : Equiv{ℓₑ}(Unit) ⦄ → IsUnit(Unit{ℓ})
  IsUnit.unit       Unit-IsUnit = <>
  IsUnit.uniqueness Unit-IsUnit = reflexivity(_≡ₛ_)

instance
  -- `Empty` is an empty type.
  Empty-IsEmpty : IsEmpty{ℓₒᵤₜ}(Empty{ℓ})
  Empty-IsEmpty = intro empty

module _ ⦃ _ : Equiv{ℓₑ₁}(T) ⦄ ⦃ empty-equiv : Equiv{ℓₑ₂}(Empty{ℓ₂}) ⦄ where
  instance
    empty-injective : Injective ⦃ empty-equiv ⦄(empty{T = T})
    Injective.proof(empty-injective) {}

  instance
    empty-function : Function ⦃ empty-equiv ⦄(empty{T = T})
    Function.congruence empty-function {()}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where -- TODO: Duplicated in Type.Properties.Singleton.Proofs
  Unit-fn-unique-value : ∀{f : Unit{ℓ} → T} → (∀{x y} → (f(x) ≡ₛ f(y)))
  Unit-fn-unique-value {x = <>} {y = <>} = reflexivity(_≡ₛ_)

module _ ⦃ equiv : Equiv{ℓₑ}(Unit{ℓ₁}) ⦄ where
  Unit-fn-unique-fn : ∀{f g : T → Unit{ℓ₁}} → (∀{x y} → (_≡ₛ_ ⦃ equiv ⦄ (f(x)) (g(y))))
  Unit-fn-unique-fn {f = f}{g = g}{x = x}{y = y} with f(x) | g(y)
  ... | <> | <> = reflexivity(_≡ₛ_ ⦃ equiv ⦄)
