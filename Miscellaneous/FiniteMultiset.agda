{-# OPTIONS --cubical #-}

module Miscellaneous.FiniteMultiset where

import      Lvl
open import Data.List using (List)
import      Data.List.Functions as List
open import Data.List.Relation.Permutation
open import Data.List.Relation.Permutation.Proofs
open import Functional as Fn
open import Type.Cubical
open import Type.Cubical.Quotient as Quotient
open import Type
open import Type.Identity

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}
private variable x y z : T

FiniteMultiset : Type{ℓ} → Type
FiniteMultiset(T) = Quotient(_permutes_ {T = T})

pattern ∅ = class List.∅

add : T → FiniteMultiset(T) → FiniteMultiset(T)
add x = Quotient.elim(\_ → FiniteMultiset _) (class ∘ (x List.⊰_)) (class-extensionalityₗ ∘ prepend)

_∪•_ : FiniteMultiset(T) → T → FiniteMultiset(T)
_∪•_ = Fn.swap add
infixr 1000 _∪•_

open import Data.Boolean
open import Data.List.Relation.Membership as List using (use ; skip)
open import Numeral.Natural
open import Relator.Equals.Proofs.Equivalence
open import Type.Cubical.Path.Equality

private variable l : FiniteMultiset(T)

count : (T → Bool) → FiniteMultiset(T) → ℕ
count f = Quotient.rec(List.count f) ⦃ {!permutes-countᵣ-function!} ⦄ -- ⦃ permutes-countᵣ-function ⦄

satisfiesAny : (T → Bool) → FiniteMultiset(T) → Bool
satisfiesAny f = Quotient.rec(List.satisfiesAny f) ⦃ {!!} ⦄ -- ⦃ permutes-satisfiesAny-functionᵣ ⦄

-- _∈_ : T → FiniteMultiset(T) → Type
-- _∈_ x = Quotient-function (List._∈_ x) ⦃ {!!} ⦄
