module Data.List.Relation.Permutation.ByInsertion.Oper.Proofs where

open import Data.List using (List)
open import Data.List.Relation.Permutation.ByInsertion
open import Data.List.Relation.Permutation.ByInsertion.Oper
import      Lvl
open import Numeral.Finite
open import Numeral.Natural
open import Relator.Equals
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}
private variable l₁ l₂ : List(T)
private variable p : l₁ permutes l₂
private variable x y z : T
private variable n : ℕ
private variable k : 𝕟(n)

sym-preserves-ins-flippedIns : (sym(ins{x = x} k p) ≡ flippedIns{x = x} k (sym p))
sym-preserves-ins-flippedIns {k = 𝟎}   {p = empty}   = [≡]-intro
sym-preserves-ins-flippedIns {k = 𝟎}   {p = ins n p} = [≡]-intro
sym-preserves-ins-flippedIns {k = 𝐒 k} {p = ins n p} = [≡]-intro
