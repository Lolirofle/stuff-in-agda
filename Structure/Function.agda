module Structure.Function where

import Lvl
open import Functional.Instance
open import Logic.Predicate
open import Logic
import      Structure.Function.Names as Names
open import Structure.Setoid
open import Type

private variable ℓ ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ : Lvl.Level
private variable A B : Type{ℓ}

module _
  (_▫₁_ : A → A → Type{ℓₗ₁})
  (_▫₂_ : B → B → Type{ℓₗ₂})
  (f : A → B)
  where

  record Compatible₁ : Stmt{Lvl.of(A) Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
    constructor intro
    field proof : Names.Compatible₁(_▫₁_)(_▫₂_)(f)
  compatible₁ = inferArg Compatible₁.proof

-- The function `f` "(behaves like)/is a function" in the context of `_≡_` from the Equiv instance.
-- `congruence` is the defining property of a function.
module _
  ⦃ equiv-A : Equiv{ℓₗ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₗ₂}(B) ⦄
  (f : A → B)
  where

  record Function : Stmt{Lvl.of(A) Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
    constructor intro
    field congruence : Names.Congruence₁(f)
  congruence₁ = inferArg Function.congruence

  {- TODO: A weird bug related to generalization appears in Lang.Vars.Structure.Operator and Structure.Operator.Proofs with the following
  Function = Compatible₁(_≡_ ⦃ equiv-A ⦄)(_≡_ ⦃ equiv-B ⦄) f
  module Function = Compatible₁{_▫₁_ = _≡_ ⦃ equiv-A ⦄}{_▫₂_ = _≡_ ⦃ equiv-B ⦄}{f = f}
    renaming (proof to congruence)
  congruence₁ = compatible₁(_≡_ ⦃ equiv-A ⦄)(_≡_ ⦃ equiv-B ⦄) f
  -}

_→ᶠⁿ_ : (A : Setoid{ℓₗ₁}{ℓₒ₁}) → (B : Setoid{ℓₗ₂}{ℓₒ₂}) → Type{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂}
([∃]-intro A) →ᶠⁿ ([∃]-intro B) = ∃(Function{A = A}{B = B})
