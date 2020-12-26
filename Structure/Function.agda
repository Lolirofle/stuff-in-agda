module Structure.Function where

import Lvl
open import Lang.Instance
open import Logic.Predicate
open import Logic
open import Structure.Function.Names
open import Structure.Setoid
open import Type

private variable ℓ ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ : Lvl.Level
private variable A B : Type{ℓ}

-- The function `f` "(behaves like)/is a function" in the context of `_≡_` from the Equiv instance.
-- `congruence` is the defining property of a function.
module _
  ⦃ equiv-A : Equiv{ℓₗ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₗ₂}(B) ⦄
  (f : A → B)
  where

  record Function : Stmt{Lvl.of(A) Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
    constructor intro
    field congruence : Congruence₁(f)
  congruence₁ = inst-fn Function.congruence

_→ᶠⁿ_ : (A : Setoid{ℓₗ₁}{ℓₒ₁}) → (B : Setoid{ℓₗ₂}{ℓₒ₂}) → Type{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂}
([∃]-intro A) →ᶠⁿ ([∃]-intro B) = ∃(Function{A = A}{B = B})
