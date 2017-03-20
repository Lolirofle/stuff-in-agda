module Relator.Equals lvl where

open import Logic(lvl)
open import Structure.Relator.Equivalence(lvl)
open import Structure.Relator.Properties(lvl)

infixl 15 _≡_
data _≡_ {T : Set} : T -> T -> Stmt where
  [≡]-intro : {x : T} -> (x ≡ x)

[≡]-elim : {T : Set} → ∀{x y : T} → ∀{f : T → Stmt} → (x ≡ y) → f(x) ↔ f(y)
[≡]-elim eq = [↔]-intro ([≡]-elimₗ eq) ([≡]-elimᵣ eq) where
  [≡]-elimₗ : {T : Set} → ∀{x y : T} → ∀{f : T → Stmt} → (x ≡ y) → f(x) ← f(y)
  [≡]-elimₗ [≡]-intro F = F

  [≡]-elimᵣ : {T : Set} → ∀{x y : T} → ∀{f : T → Stmt} → (x ≡ y) → f(x) → f(y)
  [≡]-elimᵣ [≡]-intro F = F

instance
  [≡]-reflexivity : {T : Set} → Reflexivity {T} (_≡_ {T})
  [≡]-reflexivity = [≡]-intro

instance
  [≡]-symmetry : {T : Set} → Symmetry {T} (_≡_ {T})
  [≡]-symmetry [≡]-intro = [≡]-intro -- TODO: How does this work?

instance
  [≡]-transitivity : {T : Set} → Transitivity {T} (_≡_ {T})
  [≡]-transitivity([∧]-intro [≡]-intro [≡]-intro) = [≡]-intro -- TODO: Or even this? But maybe I can ignore it for now

[≡]-with-[_] : {T : Set} → (f : T → T) → ∀{x y : T} → (x ≡ y) → (f(x) ≡ f(y))
[≡]-with-[_] f [≡]-intro = [≡]-intro

[≡]-substitution : {T : Set} → (f : T → Set) → ∀{x y : T} → (x ≡ y) → f(x) → f(y)
[≡]-substitution f [≡]-intro fx = fx

instance
  [≡]-equivalence : {T : Set} → Equivalence {T} (_≡_ {T})
  [≡]-equivalence = record {
      reflexivity  = [≡]-reflexivity ;
      symmetry     = [≡]-symmetry    ;
      transitivity = [≡]-transitivity
    }



-- testEqInstance : {T : Set} {{_ : Equivalence {T} (_≡_ {T})}} → Symmetry {T} (_≡_ {T})
-- testEqInstance {{eq}} = Equivalence.symmetry eq
-- testEqInstance2 : {T : Set} → Symmetry {T} (_≡_ {T})
-- testEqInstance2 = testEqInstance

-- testSymInstance : {T : Set} {{_ : Symmetry {T} (_≡_ {T})}} → Symmetry {T} (_≡_ {T})
-- testSymInstance {{sym}} = sym
