module Relator.Equals {l₁} {l₂} where

import      Level as Lvl
open import Functional
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Structure.Relator.Equivalence{l₁}{l₂}
open import Structure.Relator.Properties{l₁}{l₂}
open import Type{l₁}

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
[≡]-substitution : ∀{T} → (f : T → Type) → ∀{x y : T} → (x ≡ y) → f(x) → f(y)
[≡]-substitution f [≡]-intro fx = fx

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
