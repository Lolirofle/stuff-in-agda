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
  [≡]-intro : {x : T} → (x ≡ x)
  -- Interpretation:
  --   The only way to construct something of type _≡_ is to have both sides equal.
  --   When matching on the constructor, the type checker "unifies" the two terms,
  --   so that they now are the same object in the type system's eyes.
  --   This is how the builtin pattern matching by [≡]-intro works, //TODO: ...I think
  --   and therefore many propositions for equality becomes "trivial" textually.

[≡]-elim : ∀{T} → ∀{x y : T} → ∀{f : T → Stmt} → (x ≡ y) → f(x) ↔ f(y)
[≡]-elim eq = [↔]-intro ([≡]-elimₗ eq) ([≡]-elimᵣ eq) where
  [≡]-elimₗ : ∀{T} → ∀{x y : T} → ∀{f : T → Stmt} → (x ≡ y) → f(x) ← f(y)
  [≡]-elimₗ [≡]-intro F = F

  [≡]-elimᵣ : ∀{T} → ∀{x y : T} → ∀{f : T → Stmt} → (x ≡ y) → f(x) → f(y)
  [≡]-elimᵣ [≡]-intro F = F

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
[≡]-with-[_] : ∀{T} → (f : T → T) → ∀{x y : T} → (x ≡ y) → (f(x) ≡ f(y))
[≡]-with-[_] f [≡]-intro = [≡]-intro

-- Replaces occurrences of the elements in the equality
[≡]-substitution : ∀{T} → (f : T → Stmt) → ∀{x y : T} → (x ≡ y) → f(x) → f(y)
[≡]-substitution f [≡]-intro fx = fx

instance
  [≡]-equivalence : ∀{T} → Equivalence {T} (_≡_ {T})
  [≡]-equivalence = record {
      reflexivity  = [≡]-reflexivity ;
      symmetry     = [≡]-symmetry    ;
      transitivity = [≡]-transitivity
    }



-- testEqInstance : ∀{T} {{_ : Equivalence {T} (_≡_ {T})}} → Symmetry {T} (_≡_ {T})
-- testEqInstance {{eq}} = Equivalence.symmetry eq
-- testEqInstance2 : ∀{T} → Symmetry {T} (_≡_ {T})
-- testEqInstance2 = testEqInstance

-- testSymInstance : ∀{T} {{_ : Symmetry {T} (_≡_ {T})}} → Symmetry {T} (_≡_ {T})
-- testSymInstance {{sym}} = sym

-- Definition of uniqueness
Uniqueness : ∀{T} → (T → Stmt) → Stmt
Uniqueness {T} property = ∀{x y : T} → (property(x) ∧ property(y)) → (x ≡ y)
