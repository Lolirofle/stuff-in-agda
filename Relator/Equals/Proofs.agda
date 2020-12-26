module Relator.Equals.Proofs where

import      Lvl
open import Functional as Fn using (_→ᶠ_ ; _∘_)
open import Function.Names
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Propositional.Proofs.Structures
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv public
open import Structure.Setoid using (Equiv ; intro) renaming (_≡_ to _≡ₛ_)
open import Structure.Relator.Properties
open import Structure.Type.Identity
open import Syntax.Function
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂ ℓₑ ℓₚ : Lvl.Level
private variable T A B : Type{ℓ}
private variable x y : T

[≡]-coercion : (_≡_ {T = Type{ℓ}}) ⊆₂ (_→ᶠ_)
[≡]-coercion = [≡]-sub-of-reflexive

[≡]-unsubstitution : (∀{f : T → Stmt} → f(x) → f(y)) → (x ≡ y)
[≡]-unsubstitution {x = x} F = F {x ≡_} [≡]-intro

-- The statement that two functions are equal when all their values are equal are not provable.
-- Also called: Extensional equality, function extensionality.
-- [≡]-function : ∀{A B : Type}{f₁ f₂ : A → B) → (∀{x} → (f₁(x) ≡ f₂(x))) → (f₁ ≡ f₂)

[≡]-function-application : FunctionApplication A B
[≡]-function-application [≡]-intro = [≡]-intro

[≡]-with-specific : ∀{x y : A} → (f : (a : A) → ⦃ _ : (a ≡ x) ⦄ → ⦃ _ : (a ≡ y) ⦄ → B) → (p : (x ≡ y)) → (f(x) ⦃ [≡]-intro ⦄ ⦃ p ⦄ ≡ f(y) ⦃ symmetry(_≡_) p ⦄ ⦃ [≡]-intro ⦄)
[≡]-with-specific f [≡]-intro = [≡]-intro
