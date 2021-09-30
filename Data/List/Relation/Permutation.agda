module Data.List.Relation.Permutation where

import      Data
open import Data.Boolean
open import Data.List
open import Data.List.Functions renaming (module LongOper to List)
open import Data.List.Relation
open import Functional using (id ; _∘_ ; const)
open import Logic.Propositional
open import Logic
import      Lvl
open import Numeral.Finite
open import Syntax.Function
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable l l₁ l₂ l₃ l₄ : List(T)
private variable x y z : T
private variable f : A → B
private variable P : T → Bool

-- The relation for two lists that are permutations of each other.
-- This means that they contain the same elements and the same number of them but possibly in a different order.
-- Or in other words, the first list is a reordered list of the second.
data _permutes_ {ℓ} : List{ℓ}(T) → List{ℓ}(T) → Stmt{Lvl.𝐒(ℓ)} where
  empty   : ∅ permutes (∅ {T = T})
  prepend : (l₁ permutes l₂) → ((x ⊰ l₁) permutes (x ⊰ l₂))
  swap    : (x ⊰ y ⊰ l) permutes (y ⊰ x ⊰ l)
  trans   : (l₁ permutes l₂) → (l₂ permutes l₃) → (l₁ permutes l₃)

trans-swap : (l₁ permutes l₂) → ((x ⊰ y ⊰ l₁) permutes (y ⊰ x ⊰ l₂))
trans-swap p = trans swap (prepend (prepend p))

open import Data.List.Relation.Quantification
record _partitions_ (p : List(List(T))) (l : List(T)) : Stmt{Lvl.𝐒(Lvl.of(T))} where
  constructor intro
  field
    non-empty  : AllElements((¬_) ∘ Empty) p
    partitions : concat(p) permutes l

-- The permutation as a function between the permutated elements' indices.
-- Example:
--   p : [a,b,c,d,e,f] permutes [a,f,e,d,b,c]
--   map(permutation-mapping(p)) [0,1,2,3,4,5] = [0,4,5,3,2,1]
permutation-mapping : (l₁ permutes l₂) → (𝕟(length(l₁)) → 𝕟(length(l₂)))
permutation-mapping empty                = id
permutation-mapping (prepend p) 𝟎        = 𝟎
permutation-mapping (prepend p) (𝐒 n)    = 𝐒(permutation-mapping p n)
permutation-mapping swap        𝟎        = 𝐒(𝟎)
permutation-mapping swap        (𝐒 𝟎)    = 𝟎
permutation-mapping swap        (𝐒(𝐒 n)) = 𝐒 (𝐒 n)
permutation-mapping (trans p q)          = permutation-mapping q ∘ permutation-mapping p

-- TODO: It should be possible to make (_permutes_) the morphism of a category with some correct notion of equivalence (maybe trans swap swap ≡ refl for example?). Then permutation-mapping would be an instance of Functor(length) for the ((_→_) on₂ 𝕟) category?

module Proofs where
