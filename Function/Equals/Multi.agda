module Function.Equals.Multi where

open import Functional
open import Function.DomainRaise
open import Function.Names
open import Logic
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Numeral.Natural
open import Structure.Setoid.Uniqueness
open import Structure.Setoid
open import Type

private variable ℓₒ₁ ℓₒ₂ : Lvl.Level

module _ {A : Type{ℓₒ₁}} {B : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂}} where
  module Names where -- TODO: See the issue in Function.DomainRaise
    _⊜₊_ : ∀{n : ℕ} → (A ⦗ _→̂_ {ℓₒ₁}{ℓₒ₂} ⦘ B)(n) → (A ⦗ _→̂_ {ℓₒ₁}{ℓₒ₂} ⦘ B)(n) → ⦃ _ : Equiv(B) ⦄ → Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂}
    _⊜₊_ {𝟎}    f g = (f ≡ g)
    _⊜₊_ {𝐒(n)} f g = (∀{x} → (f(x) ⊜₊ g(x)))

  record _⊜₊_ {n : ℕ} (f : (A ⦗ _→̂_ {ℓₒ₁}{ℓₒ₂} ⦘ B)(n)) (g : (A ⦗ _→̂_ {ℓₒ₁}{ℓₒ₂} ⦘ B)(n)) ⦃ _ : Equiv(B) ⦄ : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
    constructor intro
    field proof : f Names.⊜₊ g
