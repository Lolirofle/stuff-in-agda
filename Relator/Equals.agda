module Relator.Equals lvl where

open import Logic(lvl)
open import Structure.Relator.Equivalence(lvl)
open import Structure.Relator.Properties(lvl)

infixl 15 _≡_
data _≡_ {T : Stmt} : T -> T -> Stmt where
  reflexivity : {x : T} -> (x ≡ x)

[≡]-reflexivity : {T : Stmt} → Reflexivity {T} (_≡_ {T})
[≡]-reflexivity = reflexivity

[≡]-symmetry : {T : Stmt} → Symmetry {T} (_≡_ {T})
[≡]-symmetry reflexivity = reflexivity -- TODO: How does this work?

[≡]-transitivity : {T : Stmt} → Transitivity {T} (_≡_ {T})
[≡]-transitivity([∧]-intro reflexivity reflexivity) = reflexivity -- TODO: Or even this? But maybe I can ignore it for now

[≡]-equivalence : {T : Stmt} → Equivalence {T} (_≡_ {T})
[≡]-equivalence = record {
    reflexivity  = [≡]-reflexivity ;
    symmetry     = [≡]-symmetry    ;
    transitivity = [≡]-transitivity
  }
