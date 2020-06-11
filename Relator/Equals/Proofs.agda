module Relator.Equals.Proofs where

import      Lvl
open import Functional using (_→ᶠ_ ; id)
open import Functional.Dependent
open import Function.Names
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Proofs.Structures
open import Relator.Equals
open import Relator.Equals.Names
open import Relator.Equals.Proofs.Equiv public
open import Structure.Setoid using (Equiv ; intro)
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Syntax.Function
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A B : Type{ℓ}
private variable x y : T

module _ where
  [≡]-substitute-type : (A ≡ B) → (A → B)
  [≡]-substitute-type = sub₂(_≡_)(Functional._→ᶠ_)

  [≡]-unelim : (∀{f : T → Stmt} → f(x) → f(y)) → (x ≡ y)
  [≡]-unelim {x = x} F = F {y ↦ (x ≡ y)} [≡]-intro

  -- The statement that two functions are equal when all their values are equal are not provable.
  -- Also called: Extensional equality, function extensionality.
  -- [≡]-function : ∀{A B : Type}{f₁ f₂ : A → B) → (∀{x} → (f₁(x) ≡ f₂(x))) → (f₁ ≡ f₂)

  -- Elimination rule for identity types.
  -- Also called J.
  -- This is interpreted as saying that all proofs of an equality are equal to each other. (TODO: Are they?)
  -- Explanation:
  --   P{x}{y} (eq-proof) is an arbitrary predicate with possible mentions of an equality proof.
  --   A value of type (∀{x : T} → P{x}{x}([≡]-intro)) means:
  --     [≡]-intro satisfies P for every pair with equal elements.
  --   The conclusion of type (∀{x y : T} → (eq : (x ≡ y)) → P{x}{y}(eq)) means:
  --     Every equality proof satisfies P for every pair there is.
  -- TODO: https://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/
  -- TODO: Usage: https://stackoverflow.com/questions/22580842/non-trivial-negation-in-agda
  [≡]-identity-eliminator : IdentityEliminator{ℓ₁}{ℓ₂}{T}
  [≡]-identity-eliminator _ proof {x}{.x} [≡]-intro = proof{x}

module _ {ℓ₁}{ℓ₂} {A : Type{ℓ₁}}{B : Type{ℓ₂}} where
  [≡]-function-application : FunctionApplication A B
  [≡]-function-application [≡]-intro = [≡]-intro

  [≡]-with-specific : ∀{x y : A} → (f : (a : A) → ⦃ _ : (a ≡ x) ⦄ → ⦃ _ : (a ≡ y) ⦄ → B) → (p : (x ≡ y)) → (f(x) ⦃ [≡]-intro ⦄ ⦃ p ⦄ ≡ f(y) ⦃ symmetry(_≡_) p ⦄ ⦃ [≡]-intro ⦄)
  [≡]-with-specific f [≡]-intro = [≡]-intro
