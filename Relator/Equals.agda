module Relator.Equals {ℓ₁} {ℓ₂} where

import      Level as Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Structure.Relator.Equivalence{ℓ₁}{ℓ₂}
open import Structure.Relator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

-- Definition of equality based on the exact representation of a data structure
-- TODO: Is this called an instance of an "intensional equality"?
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

[≡]-elimₗ : ∀{T} → ∀{x y : T} → (x ≡ y) → ∀{f : T → Stmt} → f(x) ← f(y)
[≡]-elimₗ [≡]-intro F = F

[≡]-elimᵣ : ∀{T} → ∀{x y : T} → (x ≡ y) → ∀{f : T → Stmt} → f(x) → f(y)
[≡]-elimᵣ [≡]-intro F = F

[≡]-elim : ∀{T} → ∀{x y : T} → (x ≡ y) → ∀{f : T → Stmt} → f(x) ↔ f(y)
[≡]-elim eq = [↔]-intro ([≡]-elimₗ eq) ([≡]-elimᵣ eq)

instance
  [≡]-reflexivity : ∀{T} → Reflexivity {T} (_≡_ {T})
  [≡]-reflexivity = [≡]-intro

instance
  [≡]-symmetry : ∀{T} → Symmetry {T} (_≡_ {T})
  [≡]-symmetry [≡]-intro = [≡]-intro

instance
  [≡]-transitivity : ∀{T} → Transitivity {T} (_≡_ {T})
  [≡]-transitivity([∧]-intro [≡]-intro [≡]-intro) = [≡]-intro

-- Applies functions to each side of the equality
[≡]-with-[_] : ∀{T₁ T₂} → (f : T₁ → T₂) → ∀{x : T₁}{y : T₁} → (x ≡ y) → (f(x) ≡ f(y))
[≡]-with-[_] f [≡]-intro = [≡]-intro

-- Replaces occurrences of the elements in the equality
[≡]-substitution : ∀{T} → ∀{x y : T} → (x ≡ y) → ∀{f : T → Type} → f(x) → f(y)
[≡]-substitution [≡]-intro {f} fx = fx

instance
  [≡]-equivalence : ∀{T} → Equivalence {T} (_≡_ {T})
  [≡]-equivalence = record {
      reflexivity  = [≡]-reflexivity ;
      symmetry     = [≡]-symmetry    ;
      transitivity = [≡]-transitivity
    }

-- Definition of uniqueness of elements satisfying a property
Uniqueness : ∀{T} → (T → Stmt) → Stmt
Uniqueness {T} property = ∀{x y : T} → (property(x) ∧ property(y)) → (x ≡ y)

[≡]-function : ∀{A B : Type}{f₁ f₂ : A → B} → (f₁ ≡ f₂) → (∀{x} → (f₁(x) ≡ f₂(x)))
[≡]-function [≡]-intro = [≡]-intro

[≡]-operation : ∀{A B C : Type}{a₁ a₂ : A}{b₁ b₂ : B} → (a₁ ≡ a₂) → (b₁ ≡ b₂) → {_▫_ : A → B → C} → ((a₁ ▫ b₁) ≡ (a₂ ▫ b₂))
[≡]-operation{_}{_}{_} {a₁}{a₂} {b₁}{b₂} (a₁≡a₂) (b₁≡b₂) {_▫_} =
  [≡]-elimᵣ (b₁≡b₂) {\x → (a₁ ▫ b₁) ≡ (a₂ ▫ x)} ([≡]-with-[(x ↦ (x ▫ b₁))] (a₁≡a₂))
