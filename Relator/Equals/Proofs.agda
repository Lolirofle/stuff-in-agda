module Relator.Equals.Proofs where

import      Lvl
open import Functional
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Names
open import Relator.Equals.Proofs.Equivalence public
open import Sets.Setoid using (Equiv ; intro ; Function ; BinaryOperator)
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

module _ {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} where
  -- Replaces occurrences of an element in a function
  [≡]-substitutionₗ : ∀{x y : T} → (x ≡ y) → ∀{f : T → Type{ℓ₂}} → f(x) ← f(y)
  [≡]-substitutionₗ [≡]-intro = id

  -- Replaces occurrences of an element in a function
  [≡]-substitutionᵣ : ∀{x y : T} → (x ≡ y) → ∀{f : T → Type{ℓ₂}} → f(x) → f(y)
  [≡]-substitutionᵣ [≡]-intro = id

  -- Note:
  --   The elimination rules can be used in different ways:
  --   • From (f(x) ∧ (x=y)) to f(y)
  --   • From f(x) to ((x=y) → f(y))
  -- ((x=y) → f(y)) cannot prove f(x) alone because of implication rules.

  [≡]-elimₗ = [≡]-substitutionₗ
  [≡]-elimᵣ = [≡]-substitutionᵣ

  [≡]-elim : ∀{x y : T} → (x ≡ y) → ∀{f : T → Stmt} → f(x) ↔ f(y)
  [≡]-elim eq = [↔]-intro ([≡]-elimₗ eq) ([≡]-elimᵣ eq)

  [≡]-unelim : ∀{x y : T} → (∀{f : T → Stmt} → f(x) → f(y)) → (x ≡ y)
  [≡]-unelim {x}{_} (F) = F {y ↦ (x ≡ y)} ([≡]-intro)

  -- I think this is called "Extensional equality" and cannot be proved?
  -- See:
  --   https://www.reddit.com/r/agda/comments/4te0rg/functors_extensional_equality_and_function/
  --   https://mathoverflow.net/questions/156238/function-extensionality-does-it-make-a-difference-why-would-one-keep-it-out-of
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
  [≡]-function-application : ∀{f₁ f₂ : A → B} → (f₁ ≡ f₂) → (∀{x} → (f₁(x) ≡ f₂(x)))
  [≡]-function-application [≡]-intro = [≡]-intro

  [≡]-with-specific : ∀{x y : A} → (f : (a : A) → ⦃ _ : (a ≡ x) ⦄ → ⦃ _ : (a ≡ y) ⦄ → B) → (p : (x ≡ y)) → (f(x) ⦃ [≡]-intro ⦄ ⦃ p ⦄ ≡ f(y) ⦃ symmetry(_≡_) p ⦄ ⦃ [≡]-intro ⦄)
  [≡]-with-specific f [≡]-intro = [≡]-intro

  -- [≢]-without : ∀{A : Type{ℓ₂}}{B : Type{ℓ₃}} → (f : A → B) → ∀{x y : A} → (f(x) ≢₃ f(y)) → (x ≢₂ y)
  -- [≢]-without f {_}{_} = liftᵣ([≡]-with f)
