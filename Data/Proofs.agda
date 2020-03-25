module Data.Proofs where

import      Lvl
open import Data
open import Logic
open import Logic.Propositional
open import Sets.Setoid renaming (_≡_ to _≡ₛ_)
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type
open import Type.Empty

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T : Type{ℓ}

module _ {_▫_ : Empty{ℓ} → Empty{ℓ} → Stmt{ℓ}} where
  instance
    Empty-equiv : Equiv(Empty)
    Equiv._≡_ Empty-equiv = _▫_
    Reflexivity.proof  (Equivalence.reflexivity  (Equiv.[≡]-equivalence Empty-equiv)) {}
    Symmetry.proof     (Equivalence.symmetry     (Equiv.[≡]-equivalence Empty-equiv)) {}
    Transitivity.proof (Equivalence.transitivity (Equiv.[≡]-equivalence Empty-equiv)) {}

instance
  -- `Empty` is an empty type.
  Empty-IsEmpty : IsEmpty{ℓ}(Empty)
  Empty-IsEmpty = intro(empty)

module _ ⦃ _ : Equiv(T) ⦄ ⦃ empty-equiv : Equiv{ℓ₂}(Empty) ⦄ where
  instance
    empty-injective : Injective ⦃ empty-equiv ⦄(empty{T = T})
    Injective.proof(empty-injective) {}

-- Any binary relation on Unit is an equivalence given that it is reflexive.
module _ {_▫_ : Unit{ℓ} → Unit{ℓ} → Stmt{ℓ}} ⦃ proof : (<> ▫ <>) ⦄ where
  instance
    Unit-equiv : Equiv(Unit)
    Equiv._≡_ Unit-equiv = (_▫_)
    Reflexivity.proof  (Equivalence.reflexivity  (Equiv.[≡]-equivalence Unit-equiv))       = proof
    Symmetry.proof     (Equivalence.symmetry     (Equiv.[≡]-equivalence Unit-equiv)) _     = proof
    Transitivity.proof (Equivalence.transitivity (Equiv.[≡]-equivalence Unit-equiv)) _ _   = proof

module _ ⦃ equiv : Equiv(T) ⦄ where
  Unit-fn-unique-value : ∀{f : Unit{ℓ} → T} → (∀{x y} → (f(x) ≡ₛ f(y)))
  Unit-fn-unique-value {x = <>} {y = <>} = reflexivity(_≡ₛ_)

module _ ⦃ equiv : Equiv(Unit{ℓ₁}) ⦄ where
  Unit-fn-unique-fn : ∀{f g : T → Unit{ℓ₁}} → (∀{x y} → (_≡ₛ_ ⦃ equiv ⦄ (f(x)) (g(y))))
  Unit-fn-unique-fn {f = f}{g = g}{x = x}{y = y} with f(x) | g(y)
  ... | <> | <> = reflexivity(_≡ₛ_ ⦃ equiv ⦄)
