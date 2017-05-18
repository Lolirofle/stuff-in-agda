module List.Relation {l₁} {l₂} where

import Level as Lvl
open import List
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Logic.Predicate{l₁}{l₂}
open import Relator.Equals{l₁}{l₂}
open import Type{l₂}

-- Statement of whether a list is contained in the beginning of another list
_isPrefixOf_ : ∀{T} → List(T) → List(T) → Stmt
_isPrefixOf_ prefix l = (∃ \rest → l ≡ (prefix ++ rest))

-- Statement of whether a list is contained in the end of another list
_isSuffixOf_ : ∀{T} → List(T) → List(T) → Stmt
_isSuffixOf_ suffix l = (∃ \rest → l ≡ (rest ++ suffix))
