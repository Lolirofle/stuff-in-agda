module Relator.Equals.Proofs {ℓ₁}{ℓ₂} where

import      Lvl
open import Functional
open import Lang.Instance
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂}{ℓ₂}
open import Structure.Relator.Equivalence{ℓ₁}{ℓ₂}
open import Structure.Relator.Properties{ℓ₁}{ℓ₂}
open import Type
-- import Type using () renaming (Type to Type)

module _ {ℓ₃} where
  -- Replaces occurrences of an element in a function
  [≡]-substitutionₗ : ∀{T}{x y : T} → (x ≡ y) → ∀{f : T → Type{ℓ₃}} → f(x) ←ᶠ f(y)
  [≡]-substitutionₗ [≡]-intro = id

  -- Replaces occurrences of an element in a function
  [≡]-substitutionᵣ : ∀{T}{x y : T} → (x ≡ y) → ∀{f : T → Type{ℓ₃}} → f(x) → f(y)
  [≡]-substitutionᵣ [≡]-intro = id

-- Note:
--   The elimination rules can be used in different ways:
--   • From (f(x) ∧ (x=y)) to f(y)
--   • From f(x) to ((x=y) → f(y))
-- ((x=y) → f(y)) cannot prove f(x) alone because of implication rules.

[≡]-elimₗ : ∀{T}{x y : T} → (x ≡ y) → ∀{f : T → Stmt} → f(x) ← f(y)
[≡]-elimₗ = [≡]-substitutionₗ

[≡]-elimᵣ : ∀{T}{x y : T} → (x ≡ y) → ∀{f : T → Stmt} → f(x) → f(y)
[≡]-elimᵣ = [≡]-substitutionᵣ

[≡]-elim : ∀{T}{x y : T} → (x ≡ y) → ∀{f : T → Stmt} → f(x) ↔ f(y)
[≡]-elim eq = [↔]-intro ([≡]-elimₗ eq) ([≡]-elimᵣ eq)

[≡]-unelim : ∀{T}{x y : T} → (∀{f : T → Stmt} → f(x) → f(y)) → (x ≡ y)
[≡]-unelim {_}{x}{_} (F) = F {y ↦ (x ≡ y)} ([≡]-intro)

instance
  [≡]-reflexivity : ∀{T} → Reflexivity {T} (_≡_ {T})
  reflexivity ⦃ [≡]-reflexivity ⦄ = [≡]-intro

instance
  [≡]-symmetry : ∀{T} → Symmetry {T} (_≡_ {T})
  symmetry ⦃ [≡]-symmetry ⦄ [≡]-intro = [≡]-intro

instance
  [≡]-transitivity : ∀{T} → Transitivity {T} (_≡_ {T})
  transitivity ⦃ [≡]-transitivity ⦄ [≡]-intro [≡]-intro = [≡]-intro

-- Applies a function to each side of the equality
[≡]-with : ∀{T₁ T₂} → (f : T₁ → T₂) → ∀{x y : T₁} → (x ≡ y) → (f(x) ≡ f(y))
[≡]-with f [≡]-intro = [≡]-intro

[≢]-without : ∀{T₁ T₂} → (f : T₁ → T₂) → ∀{x : T₁}{y : T₁} → (f(x) ≢ f(y)) → (x ≢ y)
[≢]-without f {_}{_} = liftᵣ([≡]-with f)

-- Applies an operation to each side of the equality
[≡]-with-op : ∀{A B C : Type} → (_▫_ : A → B → C) → {a₁ a₂ : A}{b₁ b₂ : B} → (a₁ ≡ a₂) → (b₁ ≡ b₂) → ((a₁ ▫ b₁) ≡ (a₂ ▫ b₂))
[≡]-with-op (_▫_) [≡]-intro [≡]-intro = [≡]-intro
-- [≡]-with-op-[_] (_▫_) {a₁}{a₂} {b₁}{b₂} (a₁≡a₂) (b₁≡b₂) =
--   [≡]-elimᵣ (b₁≡b₂) {\x → (a₁ ▫ b₁) ≡ (a₂ ▫ x)} ([≡]-with(x ↦ (x ▫ b₁)) (a₁≡a₂))

instance
  [≡]-equivalence : ∀{T} → Equivalence {T} (_≡_ {T})
  Equivalence.reflexivity ([≡]-equivalence) = infer
  Equivalence.symmetry    ([≡]-equivalence) = infer
  Equivalence.transitivity([≡]-equivalence) = infer

[≡]-function-application : ∀{A B : Type}{f₁ f₂ : A → B} → (f₁ ≡ f₂) → (∀{x} → (f₁(x) ≡ f₂(x)))
[≡]-function-application [≡]-intro = [≡]-intro

-- I think this is called "Extentional equality" and cannot be proved?
-- See:
--   https://www.reddit.com/r/agda/comments/4te0rg/functors_extensional_equality_and_function/
--   https://mathoverflow.net/questions/156238/function-extensionality-does-it-make-a-difference-why-would-one-keep-it-out-of
-- [≡]-function : ∀{T₁ T₂ : Type}{f₁ f₂ : T₁ → T₂) → (∀{x} → (f₁(x) ≡ f₂(x))) → (f₁ ≡ f₂)

-- Elimination rule for identity types.
-- Also called J.
-- This is interpreted as saying that all proofs of an equality are equal to each other. (TODO: Is it?)
-- Explanation:
--   P{x}{y} (eq-proof) is an arbitrary predicate with possible mentions of an equality proof.
--   A value of type (∀{x : T} → P{x}{x}([≡]-intro)) means:
--     [≡]-intro satisfies P for every pair with equal elements.
--   The conclusion of type (∀{x y : T} → (eq : (x ≡ y)) → P{x}{y}(eq)) means:
--     Every equality proof satisfies P for every pair there is.
-- TODO: https://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/
-- TODO: Usage: https://stackoverflow.com/questions/22580842/non-trivial-negation-in-agda
[≡]-identity-eliminator : ∀{T : Type} → (P : ∀{x y : T} → (x ≡ y) → Stmt) → (∀{x : T} → P{x}{x}([≡]-intro)) → (∀{x y : T} → (eq : (x ≡ y)) → P{x}{y}(eq))
[≡]-identity-eliminator _ proof {x}{.x} [≡]-intro = proof{x}
