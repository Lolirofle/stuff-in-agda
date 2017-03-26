module List.Relation where

import Level as Lvl
open import List
open import Logic(Lvl.𝟎)
open import Relator.Equals(Lvl.𝟎)

_isPrefixOf_ : ∀{T} → List(T) → List(T) → Stmt
_isPrefixOf_ prefix l = (∃ \rest → l ≡ (prefix ++ rest))

_isSuffixOf_ : ∀{T} → List(T) → List(T) → Stmt
_isSuffixOf_ suffix l = (∃ \rest → l ≡ (rest ++ suffix))
