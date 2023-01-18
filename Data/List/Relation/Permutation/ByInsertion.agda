module Data.List.Relation.Permutation.ByInsertion where

import      Data
open import Data.List as List hiding (elim ; prepend)
open import Data.List.Functions as List using (length ; insertIn)
open import Logic
import      Lvl
open import Numeral.Finite
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable l l₁ l₂ l₃ l₄ : List(T)
private variable x y z : T

data _permutes_ {ℓ} {T : Type{ℓ}} : List(T) → List(T) → Stmt{Lvl.𝐒(ℓ)} where
  empty : ∅ permutes ∅
  ins : (n : 𝕟₌(length l₁)) → (l₁ permutes l₂) → ((insertIn x l₁ n) permutes (x ⊰ l₂))

module _
  {ℓ} (P : ∀{l₁ l₂ : List(T)} → (l₁ permutes l₂) → Type{ℓ})
  (pe : P empty)
  (pi : ∀{x}{l₁ l₂}{n : 𝕟₌(length(l₁))}{p : l₁ permutes l₂} → P(p) → P(ins{x = x} n p))
  where

  elim : ∀{l₁ l₂} → (p : l₁ permutes l₂) → P(p)
  elim empty     = pe
  elim (ins n p) = pi(elim p)
