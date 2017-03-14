module Relator.Equals where

open import Logic
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties

infixl 15 _≡_
data _≡_ {T : Set} : T -> T -> Set where
  reflexivity : {x : T} -> (x ≡ x)

[≡]-reflexivity : {T : Set} → Reflexivity {T} (_≡_ {T})
[≡]-reflexivity = reflexivity

[≡]-symmetry : {T : Set} → Symmetry {T} (_≡_ {T})
[≡]-symmetry reflexivity = reflexivity -- TODO: How does this work?

[≡]-transitivity : {T : Set} → Transitivity {T} (_≡_ {T})
[≡]-transitivity([∧]-intro reflexivity reflexivity) = reflexivity -- TODO: Or even this? But maybe I can ignore it for now

[≡]-equivalence : {T : Set} → Equivalence {T} (_≡_ {T})
[≡]-equivalence = record {
    reflexivity  = [≡]-reflexivity ;
    symmetry     = [≡]-symmetry    ;
    transitivity = [≡]-transitivity
  }
