module Structure.Function where

import Lvl
open import Lang.Instance
open import Logic.Predicate
open import Logic
open import Sets.Setoid.WithLvl
open import Type

private variable ℓ ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ : Lvl.Level
private variable A B : Type{ℓ}

-- The function `f` "(behaves like)/is a function" in the context of `_≡_` from the Equiv instance.
-- `congruence` is the defining property of a function.
module _
  ⦃ _ : Equiv{ℓₗ₁}(A) ⦄
  ⦃ _ : Equiv{ℓₗ₂}(B) ⦄
  (f : A → B)
  where

  record Function : Stmt{Lvl.of(A) Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
    constructor intro
    field congruence : ∀{x y : A} → (x ≡ y) → (f(x) ≡ f(y))
  [≡]-with = inst-fn Function.congruence

-- TODO: Can this be chained? Like (A →ᶠⁿ B →ᶠⁿ C)
_→ᶠⁿ_ : (A : Type{ℓₒ₁}) → (B : Type{ℓₒ₂}) → ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ → ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ → Type{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂}
A →ᶠⁿ B = ∃(Function{A = A}{B = B})
