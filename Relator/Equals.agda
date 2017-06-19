module Relator.Equals {ℓ₁} {ℓ₂} where

import      Level as Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Structure.Relator.Equivalence{ℓ₁}{ℓ₂}
open import Structure.Relator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

-- Definition of equality based on the exact representation of a data structure
-- TODO: Is this called "intensional equality"?
infixl 15 _≡_
data _≡_ {T : Type} : T → T → Stmt where
  instance [≡]-intro : {x : T} → (x ≡ x)
  -- Interpretation:
  --   The only way to construct something of type _≡_ is to have both sides equal.
  --   When matching on the constructor, the type checker "unifies" the two terms,
  --   so that they now are the same object in the type system's eyes.
  --   This is how the builtin pattern matching by [≡]-intro works, //TODO: ...I think
  --   and therefore many propositions for equality becomes "trivial" textually.

_≢_ : ∀{T : Type} → T → T → Stmt
_≢_ a b = ¬(a ≡ b)

[≡]-elimₗ : ∀{T}{x y : T} → (x ≡ y) → ∀{f : T → Stmt} → f(x) ← f(y)
[≡]-elimₗ [≡]-intro F = F

[≡]-elimᵣ : ∀{T}{x y : T} → (x ≡ y) → ∀{f : T → Stmt} → f(x) → f(y)
[≡]-elimᵣ [≡]-intro F = F

[≡]-elim : ∀{T}{x y : T} → (x ≡ y) → ∀{f : T → Stmt} → f(x) ↔ f(y)
[≡]-elim eq = [↔]-intro ([≡]-elimₗ eq) ([≡]-elimᵣ eq)

[≡]-unelim : ∀{T}{x y : T} → (∀{f : T → Stmt} → f(x) → f(y)) → (x ≡ y)
[≡]-unelim {_}{x}{_} (F) = F {y ↦ (x ≡ y)} ([≡]-intro)

-- Replaces occurrences of an element in a function (TODO: Consider merging with [≡]-elim)
[≡]-substitution : ∀{T}{x y : T} → (x ≡ y) → ∀{f : T → Type} → f(x) → f(y)
[≡]-substitution [≡]-intro {f} fx = fx

instance
  [≡]-reflexivity : ∀{T} → Reflexivity {T} (_≡_ {T})
  [≡]-reflexivity = [≡]-intro

instance
  [≡]-symmetry : ∀{T} → Symmetry {T} (_≡_ {T})
  [≡]-symmetry [≡]-intro = [≡]-intro

instance
  [≡]-transitivity : ∀{T} → Transitivity {T} (_≡_ {T})
  [≡]-transitivity([∧]-intro [≡]-intro [≡]-intro) = [≡]-intro

-- Applies a function to each side of the equality
[≡]-with-[_] : ∀{T₁ T₂} → (f : T₁ → T₂) → ∀{x : T₁}{y : T₁} → (x ≡ y) → (f(x) ≡ f(y))
[≡]-with-[_] f [≡]-intro = [≡]-intro

-- Applies an operation to each side of the equality
[≡]-with-op-[_] : ∀{A B C : Type} → (_▫_ : A → B → C) → {a₁ a₂ : A}{b₁ b₂ : B} → (a₁ ≡ a₂) → (b₁ ≡ b₂) → ((a₁ ▫ b₁) ≡ (a₂ ▫ b₂))
[≡]-with-op-[_] (_▫_) [≡]-intro [≡]-intro = [≡]-intro
-- [≡]-with-op-[_] (_▫_) {a₁}{a₂} {b₁}{b₂} (a₁≡a₂) (b₁≡b₂) =
--   [≡]-elimᵣ (b₁≡b₂) {\x → (a₁ ▫ b₁) ≡ (a₂ ▫ x)} ([≡]-with-[(x ↦ (x ▫ b₁))] (a₁≡a₂))

instance
  [≡]-equivalence : ∀{T} → Equivalence {T} (_≡_ {T})
  [≡]-equivalence = record {
      reflexivity  = [≡]-reflexivity ;
      symmetry     = [≡]-symmetry    ;
      transitivity = [≡]-transitivity
    }

-- Definition of uniqueness of a property.
-- This means that there is at most one element that satisfies this property.
-- This is similiar to "Injective" for functions, but this is for statements.
Uniqueness : ∀{T} → (T → Stmt) → Stmt
Uniqueness {T} property = ∀{x y : T} → (property(x) ∧ property(y)) → (x ≡ y)

-- Definition of existence of an unique element satisfying a property.
-- This means that there is one and only one element that satisfies this property.
∃! : ∀{T} → (T → Stmt) → Stmt
∃! {T} property = ∃(a ↦ property(a)) ∧ Uniqueness{T}(property)

[≡]-function : ∀{A B : Type}{f₁ f₂ : A → B} → (f₁ ≡ f₂) → (∀{x} → (f₁(x) ≡ f₂(x)))
[≡]-function [≡]-intro = [≡]-intro

-- TODO: This seems to require extensional equality with functions. Create a new equality relation with an additional constructor for this case.
-- [≡]-functionₗ : ∀{A B : Type}{f₁ f₂ : A → B} → (∀{x} → (f₁(x) ≡ f₂(x))) → (f₁ ≡ f₂)
-- [≡]-functionₗ (f₁x≡f₂x) = [≡]-intro
