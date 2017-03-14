module Relator.Equals lvl where

open import Logic(lvl)
open import Structure.Relator.Equivalence(lvl)
open import Structure.Relator.Properties(lvl)

infixl 15 _≡_
data _≡_ {T : Stmt} : T -> T -> Stmt where
  [≡]-intro : {x : T} -> (x ≡ x)

[≡]-elim : {T : Stmt} → ∀ {x y : T} → ∀ {f : T → Stmt} → (x ≡ y) → f(x) ↔ f(y)
[≡]-elim eq = [↔]-intro ([≡]-elimₗ eq) ([≡]-elimᵣ eq) where
  [≡]-elimₗ : {T : Stmt} → ∀ {x y : T} → ∀ {f : T → Stmt} → (x ≡ y) → f(x) ← f(y)
  [≡]-elimₗ [≡]-intro F = F

  [≡]-elimᵣ : {T : Stmt} → ∀ {x y : T} → ∀ {f : T → Stmt} → (x ≡ y) → f(x) → f(y)
  [≡]-elimᵣ [≡]-intro F = F

[≡]-reflexivity : {T : Stmt} → Reflexivity {T} (_≡_ {T})
[≡]-reflexivity = [≡]-intro

[≡]-symmetry : {T : Stmt} → Symmetry {T} (_≡_ {T})
[≡]-symmetry [≡]-intro = [≡]-intro -- TODO: How does this work?

[≡]-transitivity : {T : Stmt} → Transitivity {T} (_≡_ {T})
[≡]-transitivity([∧]-intro [≡]-intro [≡]-intro) = [≡]-intro -- TODO: Or even this? But maybe I can ignore it for now

[≡]-with-[_] : {T : Stmt} → (f : T → T) → ∀ {x y : T} → (x ≡ y) → (f(x) ≡ f(y))
[≡]-with-[_] f [≡]-intro = [≡]-intro

[≡]-equivalence : {T : Stmt} → Equivalence {T} (_≡_ {T})
[≡]-equivalence = record {
    reflexivity  = [≡]-reflexivity ;
    symmetry     = [≡]-symmetry    ;
    transitivity = [≡]-transitivity
  }

-- TODO: For constructions/proofs of this form: Proof of a=f: a=b ∧ b=c ∧ c=d ∧ d=e ∧ e=f (also expressed as a=b=c=d=e=f)
[≡]-transitivity-chain : {T : Stmt} → Transitivity {T} (_≡_ {T})
[≡]-transitivity-chain([∧]-intro [≡]-intro [≡]-intro) = [≡]-intro
